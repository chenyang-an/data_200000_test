variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114394614937451009479361366239 : ((((((p5 → (p3 ∨ ((True → p5) ∧ p1))) ∧ p3) ∨ (True ∨ p4)) → ((p4 → False) ∨ True)) ∨ (p1 ∨ (p1 ∨ (p2 → True)))) ∨ (p5 ∧ True)) := by
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
theorem thm_5_vars_310384149991272550942394357209 : (p2 ∨ ((((((p3 ∨ p2) → p5) → p4) ∨ False) ∨ True) ∨ (((p4 → True) → p3) → (p4 ∧ ((((p4 ∨ True) ∨ (p5 ∨ p4)) ∨ p1) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181303665526456469071533708351 : ((p5 ∧ (p3 ∧ (p1 → (((False → False) → ((p4 ∨ True) ∧ p1)) → p5)))) → ((False ∧ (p1 → (False ∨ ((p2 ∨ p4) ∧ p4)))) ∨ (p3 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165629211115277227764188244706 : (((((False → p4) ∧ p1) ∨ (p1 → p1)) ∧ ((p4 ∧ (p5 → p1)) → (p4 ∧ (p3 ∨ p5)))) ∨ ((False → False) → (False → ((p2 ∧ p1) → False)))) := by
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
theorem thm_5_vars_581920510263738603778005020367 : (((p4 → (p3 ∨ (((((p1 ∧ (p1 ∨ True)) ∨ ((p2 ∨ (p5 ∨ (p5 ∨ p3))) → p3)) ∧ (p5 → (True ∧ False))) → (p1 ∧ p3)) ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623028669514329470947402003520 : ((((p5 ∧ (p3 ∧ (p1 ∨ ((p5 ∧ ((((((p2 ∨ p5) ∨ ((True → p3) ∧ (p1 → p2))) ∧ p3) ∧ p1) → p2) ∧ p5)) ∧ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_2399296093118336001241113320 : (((p2 ∧ ((p3 ∨ False) → (p1 ∧ (p1 ∨ p2)))) → (p1 ∨ True)) → (p4 → ((p2 ∧ (True → (p2 ∨ p2))) ∨ ((p4 ∧ p5) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185847714164531589985821398645 : (((((p4 ∧ ((p3 ∨ p5) → p1)) → (p3 ∨ p1)) ∨ p5) ∧ p2) → ((p1 ∧ (((p4 ∧ (p1 ∨ p3)) → False) → False)) ∨ (False → (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
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
theorem thm_5_vars_46859733835196747180204057520 : ((((p3 ∧ (((((p1 ∧ p1) → (p3 ∨ p1)) → p2) ∧ ((p4 ∧ p2) ∧ p5)) ∨ (((p4 ∧ p3) ∨ False) ∨ p3))) ∧ True) ∨ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257211167893120765258530970981 : ((p2 ∨ p2) → ((((p2 ∨ (p4 ∧ p2)) ∧ p4) ∧ p1) ∨ (p5 ∨ ((True ∧ p2) ∨ (True → ((p4 → True) → (p3 ∧ ((p4 → True) ∨ p4)))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709103925188159327290604319053 : (((((True → (p2 ∨ p3)) ∨ (p3 → (p1 ∨ p5))) → ((((True → True) ∨ True) ∨ True) ∧ (((((True ∧ p3) ∨ p4) ∨ p3) ∧ p2) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730560570764326743041812121043 : ((((p1 ∧ (p1 → p4)) → ((((False → ((p3 ∨ False) ∧ (p2 ∨ True))) → (p5 → (((p5 → True) → p2) ∨ p4))) ∨ False) ∨ (p5 → p4))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88734006092075090775695602497 : (((((p1 ∧ p5) ∧ False) → p4) → ((((((p1 ∨ ((((p1 ∨ p1) ∨ p2) ∧ p4) ∨ p1)) ∨ p3) ∧ p5) ∧ (p1 ∧ p3)) ∧ False) ∧ p4)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ p5) ∧ False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68325881294846801500067878771 : ((p3 → ((p4 → (p1 → ((((p3 ∧ True) ∧ p4) → ((True ∧ p5) → p5)) → (p5 → True)))) → (((p1 → p5) ∨ (p3 → p5)) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113169638754847580367891283806 : (((p5 → ((((p3 → ((False → (True → p5)) ∧ (p4 ∧ False))) ∨ p4) ∨ False) ∨ ((p4 ∨ ((True ∧ False) → False)) ∧ False))) → p3) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166110051381933716890031422443 : (((p4 → p5) → (((p5 ∨ p3) → (p4 → (True ∧ ((p4 → (p1 ∧ p5)) ∧ p1)))) ∧ True)) ∨ (((p4 → p4) ∨ (p3 → (p1 ∨ p4))) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187000088856660842301777530862 : ((((p4 ∨ p1) ∨ p5) → ((p1 ∧ p1) → (p4 → (p5 → p4)))) → (((((True → (p2 ∨ ((True ∨ False) ∧ p5))) ∧ p5) ∧ True) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328802519061332644461070420781 : (True → ((p4 ∧ ((p1 ∨ ((p5 ∧ (False ∧ True)) ∨ False)) ∨ p2)) ∨ ((p5 → (((p2 ∨ p2) ∧ True) → p1)) ∨ ((p2 → p4) ∨ (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234513200062789860855356910266 : ((p2 → (p2 → True)) → (((((p2 → (p3 ∧ ((p3 ∧ p1) ∧ p3))) ∧ True) ∨ p4) ∨ (p4 → (p2 → (((False → p1) ∧ p5) ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611256733756212536826491656019 : ((((((p4 → p4) ∧ ((p4 ∨ p1) ∨ (((p5 ∧ False) → (p1 ∧ (p2 ∧ p2))) ∧ ((False ∧ p5) → ((p3 ∧ True) ∧ p2))))) → p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_351968309047957987226807972982 : (p4 → (((p4 → (True → (False ∨ p5))) ∨ (p3 ∨ p4)) ∧ ((False ∨ False) ∨ (((((p1 ∨ True) ∧ True) ∧ (p2 → (p4 → p3))) ∨ True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655975239489161230645582043111 : ((((((True ∧ (((p3 ∨ ((p3 → (p3 ∨ True)) ∨ True)) ∧ (p5 ∧ p2)) ∧ p5)) ∨ p1) ∨ (((p4 ∧ p1) ∨ p3) → p2)) ∨ (p3 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_257385548913033477645852240028 : ((p2 ∨ p5) → (((((True → False) ∧ p1) ∧ (p4 ∧ (p4 → ((True → (False ∧ p3)) ∨ True)))) ∧ (p3 → p5)) → (((False ∨ False) ∨ p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h16.left
  let h20 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h23 := h17 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h26 := h17 h25
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310402813597233418631117640886 : (p2 ∨ ((p1 ∧ ((True ∨ (p4 → (p1 ∧ p4))) → False)) ∨ (((((((p4 → p5) ∨ True) ∧ (p4 → True)) ∨ False) ∨ True) ∨ (p3 → p5)) ∨ p2))) := by
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
theorem thm_5_vars_330497724598015610423800012119 : (True → (p4 ∨ ((((p3 ∨ (p2 ∨ p5)) ∨ p1) ∧ ((p3 ∨ (((False ∨ p5) → p3) ∧ p5)) ∨ p4)) ∨ (True ∧ ((p1 ∧ (p3 ∧ p3)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234731489730137417701334476208 : ((p4 → (p5 ∨ p4)) → (p3 ∨ (p5 ∨ (((p2 → p5) ∧ p4) → ((p5 → ((True ∨ (p4 → False)) ∧ ((True ∨ False) → (False ∨ p2)))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225946905640296236542769227262 : (((p2 ∧ p4) ∨ p3) ∨ (((((p3 ∧ p1) → True) → p3) ∨ ((((True ∨ p2) → (p4 ∨ p4)) ∧ True) ∨ ((p1 ∨ True) → True))) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69182498561851034946551134593 : ((p5 → ((p5 → ((p4 ∧ True) ∨ ((False ∨ (True ∨ p2)) → ((p2 ∧ False) ∧ p4)))) ∨ (p5 ∨ (((True ∧ (True → False)) ∧ p1) ∧ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113514111052603172650782668994 : ((((p3 ∨ ((p1 ∧ p1) ∨ (((False ∧ p1) ∧ p2) ∧ (p3 ∧ True)))) ∨ (((False ∨ False) ∨ p3) → (p2 ∨ True))) ∨ (p2 → p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114094698173962789764263294960 : (((True ∧ (((p1 → p2) ∧ ((((False ∧ False) → p5) ∧ p4) → (p3 → ((True ∨ p1) ∧ p3)))) → p2)) ∨ (p2 ∨ (p1 ∨ p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316742873444795934034053731744 : (p3 ∨ (True → ((p2 ∨ ((((((((True → False) ∨ (True ∧ p1)) → (p3 ∨ False)) ∨ p5) ∧ (p5 ∧ True)) → False) → False) ∧ p2)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_35241979980031977439880756359 : ((p1 → (p1 ∧ ((p2 ∧ ((True ∨ p4) ∨ p1)) → (((((p2 ∧ p4) ∨ True) → ((p4 → False) ∨ p5)) ∨ (False ∧ True)) ∨ (p2 ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246509215290701579978842698388 : ((p5 ∧ p1) ∨ ((p5 → ((((p1 ∨ p2) ∨ p4) → (False ∧ (p5 ∨ p2))) ∨ (((((p4 ∨ p5) ∨ p5) ∧ p4) → p4) ∨ True))) ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602980956272441872467850811352 : ((((p1 ∨ ((p3 → (True ∧ p2)) ∨ (((p1 → (p3 ∨ ((p4 → (((True → p4) ∨ (False ∨ p5)) ∨ p5)) ∧ p2))) ∧ p1) ∧ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160494675379572429940276489499 : ((((p5 → ((((p4 → True) ∨ p3) ∧ p3) → (p3 → True))) → False) ∧ ((p4 → True) → (p2 ∨ p4))) → ((p5 → p4) ∧ ((p4 ∨ True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → ((((p4 → True) ∨ p3) ∧ p3) → (p3 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : (p5 → ((((p4 → True) ∨ p3) ∧ p3) → (p3 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h18 := h12 h14
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674101266360849021586123725857 : ((((p2 ∧ ((p3 → p5) → (((p3 ∧ (p3 ∨ p1)) ∨ ((True ∨ False) → p4)) → (False ∧ ((False → p5) ∧ True))))) → (p3 ∨ (p4 ∨ True))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59356908867072416553062368770 : (((p5 ∨ p2) ∨ ((p1 → ((p5 ∧ p2) ∨ (((p1 ∧ (((((True ∨ False) → p2) → False) → (False → True)) → p3)) → p2) → True))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62710891099762443391513475865 : ((p4 ∧ (((True ∨ p3) ∨ ((p3 → ((((False ∨ True) → p4) → (False ∧ p2)) ∨ (((True ∨ p2) → p3) ∧ (p1 → False)))) ∨ p1)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706761906093491976689725022280 : ((((((p1 → ((True ∨ p3) ∧ p5)) → p4) ∧ p3) ∨ (True ∧ ((p1 ∨ (((((p3 → p3) → False) ∧ p5) ∨ p4) ∧ p3)) ∨ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191286331758854722117150463549 : (((p5 ∨ True) ∧ (p2 ∧ (p3 ∨ (False → (False → p2))))) ∨ (((p3 → (True → ((p5 → p1) ∧ p5))) ∧ p4) ∨ (((False → True) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116038114920976102189860865025 : (((p2 ∨ (p5 ∧ (False → p2))) → (True → (((((p3 ∧ (p3 → False)) ∧ p1) ∧ ((p3 → p2) ∧ p5)) ∨ (p3 ∧ p5)) ∧ p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69268889732280709468653095250 : ((p5 → ((p2 ∧ p1) ∨ (((((p3 → p3) → p1) ∧ p2) ∨ p5) → (p3 → (False ∨ (p1 ∨ (True ∧ (p1 → (False → (p2 ∨ p3)))))))))) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684481536876183596717144817133 : ((((((p3 ∨ p3) ∧ (p4 ∨ (p4 → True))) ∧ (True → ((p5 ∧ True) ∨ (True ∧ (True ∨ p4))))) ∨ ((p2 ∨ (False → (True ∨ p5))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256683861454592531517059615133 : ((p1 ∨ False) → (p3 ∨ (((p2 ∨ ((((p3 ∨ ((False ∧ True) ∧ (p2 → False))) ∨ p1) ∨ (False → (p2 ∨ False))) ∨ p1)) ∨ (p4 ∧ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159895778826051649072109033317 : ((((((p4 → (p4 → p2)) → (p3 → (p1 ∧ ((p2 → p5) ∧ p2)))) ∨ (p3 → p3)) ∨ p5) → p1) → ((p1 ∧ ((False ∧ p3) ∨ p1)) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216347681931427958897159322538 : ((p3 → ((p4 ∨ p4) ∧ p2)) ∨ (p2 ∨ (((p4 ∨ (p1 ∧ (True ∧ p2))) ∧ (p4 ∧ p3)) → ((p2 ∨ ((True ∧ True) ∧ p1)) → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h22.left
      let h32 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259008364410370540550146327668 : ((True → p4) → (((True → ((p4 ∨ p4) ∧ p5)) ∧ ((False ∨ (p5 ∨ ((False ∨ (p2 ∧ (True → p2))) ∨ ((p5 → p3) ∧ p4)))) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147405932773694705989597296034 : ((((p1 ∨ (((p2 ∧ True) ∧ p3) → p3)) → ((p2 ∧ (((p5 ∨ p4) → True) ∧ (p5 → p5))) → p4)) ∨ False) ∨ (((p4 ∧ p5) → p4) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67806127768865435499800021121 : ((p2 → ((((((p3 ∧ True) ∧ p2) → True) ∨ (p4 → p4)) ∨ (p4 ∨ ((((p4 ∧ p3) → (False ∧ p2)) ∧ True) ∨ (p2 ∨ p1)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68435030646679436288306056600 : ((p3 → ((p5 ∨ p2) → ((p4 ∨ p3) → (True ∧ ((p4 ∨ p2) ∨ ((p5 ∧ p1) ∨ (False ∨ ((p3 ∧ (p3 → (False ∧ p5))) ∨ p4)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55931183301725957301195346668 : (((p1 → (p4 ∨ (p1 ∧ p3))) ∧ (p3 ∨ (((p5 ∧ ((((p1 → (p2 ∧ (p1 ∧ p2))) → (p3 ∨ False)) ∧ p3) → False)) ∧ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207153678827975301348810492623 : (((p2 → ((True → p4) → p3)) ∧ p5) → (True → (((p3 ∧ True) → (p4 ∨ ((p4 ∧ True) ∨ p2))) → (((p3 ∧ (True ∧ p4)) → p4) ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160007413392235921287071849252 : ((((True ∧ ((p3 ∨ p5) → p5)) ∨ ((p1 ∧ (p5 ∧ (p4 → (p2 → (p1 → p3))))) → False)) → p3) → (((p2 → False) → (p2 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61496665867755394221583912134 : ((p1 ∧ ((((((p4 → p2) ∨ p5) ∧ p5) ∧ ((p3 ∧ p5) ∧ p5)) ∧ ((p1 ∧ ((False ∨ True) ∧ True)) ∧ p3)) → ((True ∧ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262347177707136893283857537733 : (True ∧ (((p1 → (False ∧ (False ∧ p1))) ∨ ((p5 → ((((True → p1) ∧ p2) → (p1 ∧ False)) ∨ (p2 ∨ p1))) → (p1 ∧ (p3 ∨ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46728113541567906491162321300 : (((True → (((p2 → False) → ((((True → p3) ∧ False) → True) ∨ p1)) → (((False ∨ (p5 → False)) ∨ p4) ∨ (p5 → p3)))) ∧ (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46947288059424803127724343684 : ((((True → ((((((p3 ∨ (p5 → p3)) → p5) ∨ p5) → p3) → p2) ∧ ((((p2 ∨ p3) ∨ True) → p3) → p3))) ∨ True) ∨ (p2 ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42576878313516831228231218078 : (((p2 ∨ (((((p4 ∧ (p4 → (p5 → p1))) ∨ p2) ∨ ((p2 ∧ p2) ∧ (p3 ∧ (p1 → p3)))) → (p3 → p5)) ∨ (False ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50409206537336780055774950273 : (((False ∧ ((((p2 → p4) ∨ p1) ∧ p3) ∨ ((p3 ∧ (p2 ∧ (((p2 ∨ p5) ∨ p1) → p2))) ∧ True))) ∨ ((p1 → (p3 ∨ p4)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112050742398205107618062892012 : ((((p1 → (p1 ∧ p4)) → (((p1 → ((((((p4 ∧ p2) ∧ True) ∨ p3) ∧ (p4 ∧ True)) ∧ p3) ∧ False)) → p3) ∨ True)) ∨ False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609054686102575324040981202294 : ((((((((p1 ∨ p1) ∨ p1) → ((p2 → p4) ∧ p3)) ∨ (p2 ∨ ((((p3 → p1) → False) → ((False ∧ p2) ∧ True)) ∨ False))) ∨ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329709424026603968529672513214 : (True → ((False → False) → ((((p4 ∨ (p2 ∨ (True ∨ (p1 ∧ (p3 → p1))))) ∨ (p4 ∧ p1)) → (p1 ∧ False)) → (p4 → (p2 ∧ (p4 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ (p2 ∨ (True ∨ (p1 ∧ (p3 → p1))))) ∨ (p4 ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∨ (p2 ∨ (True ∨ (p1 ∧ (p3 → p1))))) ∨ (p4 ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116377801842634976653257435169 : ((((False → p2) → False) → (((((p1 ∧ p1) ∧ (p4 → ((False ∨ (p5 ∧ (p4 → (p5 → False)))) ∨ p4))) → False) ∧ p5) ∨ p2)) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158012002824506868870784704564 : ((((p2 ∧ (False ∨ (p4 ∧ p4))) ∨ p3) ∧ (False → ((((False ∧ p1) → p1) ∨ p4) ∨ (p2 ∨ False)))) ∨ ((p2 ∨ ((False → p1) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241577070420571727402962003260 : ((False → p4) ∧ (((((False ∨ p4) ∨ (p2 ∧ False)) ∧ (p1 → (p3 → ((True → ((p3 → p5) ∧ (p1 → p2))) ∨ (p1 ∨ p4))))) → p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256726288000462985159140903019 : ((p1 ∨ p1) → ((p5 ∨ ((True → (p4 → False)) → p2)) → ((p2 ∨ (p2 ∧ p5)) → (False ∨ (p2 ∨ (((True → p3) ∨ False) ∨ (p5 → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54992505995388330015696435274 : ((((p5 ∧ p1) ∨ ((p5 ∨ p4) → False)) ∧ (((p2 → True) ∧ ((p4 ∧ (((p4 ∨ False) ∨ True) ∧ (False ∧ p1))) ∨ p3)) → (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159111972896553946176581558903 : ((True → (p1 → ((((p2 ∨ (p4 ∨ p3)) → (p3 ∧ (True ∧ p2))) ∨ (False → True)) ∧ (True ∧ p4)))) ∨ ((p4 ∧ p5) → (False → (True ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66077431334650941439232923224 : ((p5 ∨ ((p5 ∧ ((p2 → ((((p5 ∨ ((True ∨ p2) ∧ ((p2 ∧ p5) ∧ False))) → (p5 ∨ False)) ∨ True) → p3)) → (p3 ∧ False))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37479763668198276145388639181 : (((((((p5 → p1) → p1) ∧ True) ∨ (((False → p2) → p1) ∨ (p1 ∧ (((True → (p4 ∨ True)) ∧ p2) ∧ (True → True))))) ∨ False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39312502473370251829385021312 : (((p1 ∧ (p4 → (False ∧ (p1 ∧ ((((p5 ∨ p3) ∧ ((False ∨ ((p1 ∨ True) ∧ p4)) → True)) ∨ (p3 → (False → p5))) ∨ True))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175509198456541954009987589608 : ((p3 → (p2 ∧ (((p1 → (((p1 → (p4 ∨ p4)) → p2) ∨ p4)) ∧ False) → False))) → ((((p2 → (p4 → (p4 → False))) ∧ False) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694014983881400011923193933496 : ((((((False ∧ (p2 → True)) ∨ (True → (p4 ∨ (p1 → p5)))) → (p5 ∧ False)) ∨ ((p5 → p5) ∨ (True ∨ (True ∨ ((p1 → p2) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81047692388635132917913122223 : (((((p1 ∧ (p1 ∨ p4)) ∧ ((p3 ∨ True) → False)) ∧ ((p1 ∧ False) → ((False ∨ False) → ((p2 ∧ p4) ∨ p2)))) ∧ (p3 ∧ (False ∨ p1))) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315234351961705597013516166339 : (p3 ∨ ((((p4 ∧ p5) ∨ p3) ∨ False) ∨ ((False → (((p5 ∨ (p3 ∨ (p5 ∧ (True ∨ (p4 → p5))))) → (True ∨ (p4 ∧ p5))) ∨ p3)) ∨ p4))) := by
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
theorem thm_5_vars_47583603048966515454432852518 : (((p2 → ((((p3 → p4) → (((((True → (False → (True → p3))) ∧ True) → (p4 ∧ p3)) → p4) ∨ p2)) → p3) ∨ p1)) ∨ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37228805716881244558922319658 : (((((p3 → False) ∧ ((((((p3 → False) ∨ p3) → p4) → p3) ∧ True) ∨ (p3 ∨ ((p5 ∧ ((p5 → p1) ∨ p2)) → p5)))) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40027297779493094492271585589 : (((((((((False → False) ∨ (p4 → (((True ∧ p3) → (p4 ∨ (p2 ∨ True))) ∧ p3))) → p1) ∨ (False ∧ p1)) → p3) ∧ True) ∧ True) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136133418848133490371254530883 : (((((True ∧ ((p5 → p3) ∧ p2)) ∨ True) ∨ p1) → (False ∨ ((p5 ∨ ((True → ((p5 ∧ True) → p4)) ∧ False)) ∨ True))) ∨ (p3 ∨ (True → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62617465781283355933245143056 : ((p4 ∧ (((p4 ∨ ((((p1 → p5) ∨ ((p4 → (True ∨ p1)) ∧ p1)) ∨ (p4 ∧ True)) ∨ (False ∨ (p5 → p1)))) ∧ (True → False)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177995658671890399739477402247 : (((False ∨ (((p2 ∨ True) → ((False ∨ p1) ∨ (p4 ∨ p4))) ∨ p3)) ∨ p2) ∨ (((True → (False → True)) ∧ ((p1 ∨ p1) ∧ (p5 → p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111419027093270249942738916221 : (((p3 ∨ ((False ∨ (p1 → p3)) ∨ (p5 ∨ ((p4 ∧ True) ∧ (((p3 → p1) → (p3 ∨ ((p2 ∨ p4) ∨ p4))) ∧ True))))) ∧ p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611828334968088319587940224441 : (((((p3 → (((p3 → p1) ∨ (((((False ∧ (p4 → (p5 ∧ False))) ∨ ((p2 ∨ p3) → p1)) ∧ p1) ∨ True) ∨ p5)) ∨ p4)) → p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_298787263122584315683772750113 : (False ∨ (((((p1 ∧ (((p5 → p3) → (((p4 ∧ p2) ∨ (p3 ∧ p4)) ∨ (p4 → (p4 ∨ p4)))) ∨ p2)) ∧ True) → p5) ∨ (True ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111333919632972580129105315110 : (((p2 ∧ (p5 ∨ (((p3 → p5) ∧ ((p2 ∨ (False ∧ (p5 ∧ p1))) ∨ ((p5 ∨ (p1 → p3)) ∧ (False → p3)))) ∨ p3))) ∧ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113555136278474408970640571850 : ((((p1 ∧ p1) ∧ (((True ∨ (p3 ∧ p4)) ∨ ((p1 → p4) ∨ (False ∧ p2))) ∧ ((p3 → (p4 ∨ p4)) ∨ False))) ∨ (True ∨ p5)) ∨ (True ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54992535665200163925810808368 : ((((p5 ∧ p1) ∨ (p4 ∨ (p4 ∧ p5))) ∧ ((p3 ∧ p2) → (p4 ∨ ((p5 → (((p1 → p2) ∨ p1) ∧ (True → (p1 ∨ p3)))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51129734744362460455925114237 : ((((p5 ∧ (((p3 ∧ ((p1 ∧ ((p1 ∧ p3) ∧ True)) ∨ p1)) ∨ p4) ∧ (p3 ∨ p4))) ∨ True) ∨ ((((p1 ∨ p4) ∧ p1) ∧ p5) → False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113036377334405072046675138977 : (((False ∨ ((((((p5 → (p5 ∧ True)) ∨ p5) ∧ p3) ∧ ((p5 → p3) ∨ (p4 ∨ p4))) ∧ p2) ∧ (p2 ∧ (p3 → p2)))) → p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215946615999374226584092296226 : ((p4 ∨ ((p3 ∧ p3) ∧ False)) ∨ ((p3 ∨ (((p5 ∨ (p4 ∨ p3)) ∧ p2) ∨ p3)) ∨ (((False ∧ ((True ∨ p4) → (p3 → p5))) ∨ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47002140673714654670659323354 : ((((((False → True) ∧ p2) → (True → ((((p2 ∨ p3) ∨ p3) ∨ p5) ∨ (p2 ∨ (p4 ∨ ((p3 ∧ p5) → False)))))) → p1) ∨ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747902071569413408874751744373 : ((((False → p4) → (p4 ∨ (p4 ∧ ((False ∨ True) ∧ ((p1 ∧ ((p1 ∨ ((p3 ∧ p4) ∧ p5)) ∧ p4)) → (((p1 → p5) → True) ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117653600502952552430854791518 : ((p3 ∧ (((p2 ∧ ((p2 ∨ p2) ∨ p3)) ∨ ((p5 ∨ False) → (((p4 → (False ∨ p4)) ∨ True) ∨ (p3 ∨ True)))) ∨ (p2 ∧ p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624315501824168643030814403152 : ((((p3 ∨ ((p4 → ((p3 → True) → (p3 ∨ (False ∨ (p4 ∧ (True → (False ∧ p1))))))) ∨ (p4 ∧ (((p5 → True) ∨ False) ∨ p2)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180157277085848973045078834850 : ((((p3 ∨ ((p3 ∨ True) → ((p1 ∧ False) ∧ p4))) ∨ (True ∧ True)) → False) → (p3 ∨ (p2 ∧ (p1 ∧ (((p2 ∧ p3) → p3) → (True → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((p3 ∨ True) → ((p1 ∧ False) ∧ p4))) ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615392306164895054970711337927 : ((((((p3 → p5) → ((((False → p1) ∧ p1) → (p1 ∨ False)) → (p1 → (p2 → p3)))) ∨ (p5 → (False → ((p4 ∧ p1) ∨ p3)))) ∨ False) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116708157898810717423884389246 : (((p1 ∧ p2) ∨ ((p3 ∨ (p2 ∧ p5)) ∨ ((p5 ∧ ((p1 ∨ (False ∨ ((p5 ∨ p3) → True))) → (p4 ∧ p3))) → (True ∧ True)))) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_218305930295412654415773147739 : (((p5 ∨ p1) ∨ (True ∧ False)) → (p1 ∨ ((p1 ∧ (p4 ∨ p1)) ∨ (False ∨ ((False ∨ ((p3 → False) → (((True ∨ p4) → p3) ∧ p1))) ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353412494200377458533745517653 : (p4 → (p1 ∨ (((False ∨ (p3 ∧ (True ∨ (p2 → p5)))) ∧ ((False ∨ (p2 ∧ (False ∧ (((p1 ∨ p2) → True) ∧ p5)))) ∧ (p1 ∧ p2))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67840168604673223604154303882 : ((p2 → ((((True ∧ (p1 ∨ ((((p4 ∨ (p3 ∨ p4)) ∧ p3) → p2) ∨ True))) → (p3 ∧ True)) ∨ (p5 ∧ (p3 → p4))) ∨ (True → p2))) ∨ p5) := by
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



