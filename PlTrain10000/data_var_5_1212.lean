variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602034269364200986676772459701 : ((((p5 ∧ (((((p4 → p2) ∧ ((((p5 → p2) → True) → p3) → ((p2 ∧ (True ∧ (p2 ∧ False))) ∨ p4))) → p3) ∧ p5) → p3)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60193951069583288351362533434 : (((p5 ∨ p4) → (((((((p4 ∨ p4) → p1) → (p4 → ((p3 ∧ p3) ∨ p3))) ∨ p2) → p3) ∧ (False ∨ (p1 → (False ∨ p2)))) ∨ True)) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192770375112509990786580158936 : (((p3 ∧ ((p3 → p5) ∨ ((False → p3) → p1))) → p5) → ((False → p2) → (((True ∧ p1) ∨ (p4 ∨ (p3 ∨ ((False ∨ p4) ∨ True)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_50432974063528609346745991804 : (((p5 ∧ (p5 ∨ (((((p1 → ((False ∧ p5) → p2)) ∧ False) ∧ (p3 ∧ False)) ∧ (p5 → p5)) ∧ True))) ∨ ((False → p1) ∨ (p1 ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321971070539585529537465851441 : (p5 ∨ (((p1 ∨ (((p2 ∧ p4) ∧ (((True ∧ (True → p2)) ∨ p2) ∨ p3)) ∧ False)) ∨ ((p4 → (True ∨ True)) ∨ ((p3 ∨ p4) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_687342129041718140289010615589 : (((((p5 ∧ (p3 → (((p1 ∨ p2) ∨ p3) ∨ (True → (p3 ∧ (p4 ∨ p4)))))) ∧ p4) ∧ (((True → p5) → p3) → (p4 ∨ (True ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243962372340998643911246012746 : ((True ∧ p1) ∨ (((p1 ∨ ((True ∨ p4) → ((False ∧ False) ∧ True))) ∧ (p2 → (((True → p1) ∨ p4) → (False → p2)))) → ((True ∧ p3) → p1))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310508654322725587616068961941 : (p2 ∨ ((p2 ∧ (p4 ∧ (False ∨ (True ∧ False)))) ∨ ((p5 ∨ (p1 → (((p3 ∨ p3) ∧ (False → (p3 ∨ (p5 ∨ (True ∧ p1))))) → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49768469701511862687321576623 : (((p1 ∨ (((p2 → (p2 ∧ p3)) → (False → ((p3 → ((False ∧ p4) ∨ p4)) → (p1 ∧ (p1 → p1))))) → p2)) → ((p1 ∨ False) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 → (p2 ∧ p3)) → (False → ((p3 → ((False ∧ p4) ∨ p4)) → (p1 ∧ (p1 → p1))))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694755031163067787771743915135 : ((((p4 ∨ (True ∧ (p1 ∨ ((p2 → p1) → (((p1 ∨ p2) ∨ p5) ∨ p5))))) ∨ ((p4 ∧ p5) ∨ ((False → True) ∨ (False ∧ (False ∧ True))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310940606863655484691982850697 : (p2 ∨ ((False ∨ True) ∧ (((p2 → p2) → ((((p3 ∨ p4) ∨ (p4 ∧ True)) ∨ (((False → p4) ∨ p2) ∨ (p4 → (p1 ∨ p2)))) ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187325357091270747498665555256 : ((p2 ∧ (((True ∨ p5) → ((False → (p1 → True)) ∨ p4)) ∧ p1)) → ((p3 → p2) → ((p3 → False) ∨ ((True → True) ∨ ((p2 → p2) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135035541624695191890981432893 : (((((p1 → (((p4 → (p5 ∧ p2)) ∧ p5) → False)) ∨ (((p4 ∧ p5) → p4) ∧ (p3 → False))) ∧ True) ∨ (False → False)) ∨ (p4 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46867284177232795281016669226 : ((((p3 ∨ ((False → True) → (((((p3 → p4) ∧ p3) ∧ p3) ∨ p4) ∨ ((((p1 → p5) ∧ p2) ∧ False) ∧ True)))) ∧ p4) ∨ (False → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55570183563123144096063934247 : (((True ∨ ((p1 ∧ True) ∨ (p3 → p4))) → (((((p3 ∨ p5) ∨ p2) ∧ False) ∨ ((False ∨ False) ∧ (False ∨ ((True ∨ p3) ∨ p4)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873114203835652608643834793255 : ((((p1 → ((False ∨ p2) ∨ (((True → (p3 ∨ (p4 ∧ p5))) ∧ (p1 ∨ ((True ∨ p2) → (False ∨ (p4 → (p1 → p1)))))) ∨ p1))) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((False ∨ p2) ∨ (((True → (p3 ∨ (p4 ∧ p5))) ∧ (p1 ∨ ((True ∨ p2) → (False ∨ (p4 → (p1 → p1)))))) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37733920652348494556687125463 : ((((((((p4 ∧ p2) → ((p3 → p3) → p5)) ∧ p5) ∨ p2) ∨ ((p5 → (False → ((p5 → (p3 ∧ False)) ∨ p4))) → p2)) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66247930230014357070556194997 : ((p5 ∨ ((True → (p1 ∨ (p4 ∨ (False → p3)))) → (((p5 → ((((p3 ∧ p1) → False) ∧ (True ∧ True)) ∨ False)) → False) ∧ (False → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46014896594010856091918755060 : (((((((True ∨ True) ∧ p4) → (p1 ∨ p1)) ∨ (p4 ∨ (p3 → (True → (p2 ∧ (p3 ∧ ((p1 ∨ p4) ∧ p2))))))) ∧ p2) ∧ (p4 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652029820792881801324592694863 : ((((False ∧ ((((False → p4) ∧ (((p1 ∧ p5) → False) ∧ False)) ∧ (((p5 ∧ (p1 ∧ p5)) ∨ p1) ∧ (p2 → p1))) ∨ p3)) ∧ (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306668342614428005389088035781 : (p1 ∨ (True ∧ ((p3 ∨ p1) ∨ ((p3 → p4) ∨ ((True ∧ p4) → (p3 → (True ∧ (p2 ∨ ((True ∧ False) ∨ (False → (p5 ∧ (p3 ∨ p4)))))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177675262715922289509033061651 : (((((False ∧ (p2 → ((p2 ∨ p2) ∨ True))) → (True ∨ p4)) → p2) ∧ True) ∨ (p4 → ((p5 ∨ (p1 → p1)) ∧ (((True ∨ p5) ∧ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135965826596870269328324432458 : (((p5 ∨ (((p1 → (True ∨ (p4 ∧ p2))) → p1) → p5)) ∧ ((p3 → (((p4 ∨ p3) ∧ (p1 ∧ p2)) → p5)) ∨ False)) ∨ (p1 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45768868157054775898882668896 : (((False → (p5 ∧ ((p1 ∧ p5) → ((True ∧ ((((p1 → p5) → p5) ∧ p4) → (((p5 ∧ (p1 → p5)) ∨ False) ∧ p5))) ∧ p4)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619393277335752655791420837255 : (((((True ∧ (p4 → p1)) → (p3 → (((p3 → p2) → (p1 ∧ ((True → False) → (((p5 ∧ p2) ∨ p4) → (p3 ∨ p1))))) → p4))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185351141294183472634432157948 : ((p4 ∧ ((p2 ∨ (p4 → p5)) ∧ ((True → (p2 ∧ p3)) ∨ p5))) ∨ (((p3 ∨ False) → (((p5 → p4) ∨ (False ∧ False)) ∨ True)) ∨ (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159950455364565249994783005882 : ((((False ∧ ((p4 ∨ False) ∧ (True ∧ (True ∨ (p3 ∧ (p4 → (p2 ∧ p5))))))) ∨ (p5 ∨ False)) → p3) → ((p4 ∧ ((p4 ∨ True) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914582684525905044566903089768 : ((((((p5 ∨ (False ∨ p4)) → p2) ∧ (((p5 ∨ (p2 ∨ (True → p2))) ∨ False) ∨ p2)) ∧ ((p1 → (p2 ∧ ((p3 → p2) → p4))) ∧ p1)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h3.left
        let h10 := h3.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h11 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h11
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : (p3 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h16 : (p5 ∨ (False ∨ p4)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h17 := h4 h16
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h18 := h13 h14
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h3.left
          let h22 := h3.right
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h23 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h24 := h21 h23
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h26 : (p3 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h27
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h28 := h25 h26
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h3.left
          let h31 := h3.right
          -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
          have h32 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h30, we can now drive its conclusion.
          let h33 := h30 h32
          -- We need to get the right conjuct of h33 based on <expert-advice>.
          let h34 := h33.right
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : (p3 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h36
            -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
            have h37 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h29, we can now drive its conclusion.
            let h38 := h29 h37
            -- One of the premise coincides with the conclusion.
            exact h38
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h39 := h34 h35
          -- One of the premise coincides with the conclusion.
          exact h39
    case inr h40 =>
      -- False on the left can always be used.
      apply False.elim h40
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h3.left
    let h43 := h3.right
    -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
    have h44 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h43
    -- We have shown the premise of h42, we can now drive its conclusion.
    let h45 := h42 h44
    -- We need to get the right conjuct of h45 based on <expert-advice>.
    let h46 := h45.right
    -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
    have h47 : (p3 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h48
      -- One of the premise coincides with the conclusion.
      exact h41
    -- We have shown the premise of h46, we can now drive its conclusion.
    let h49 := h46 h47
    -- One of the premise coincides with the conclusion.
    exact h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22106296315364718929445731674 : (((((False ∨ (p5 ∨ p5)) ∧ False) ∧ (True ∧ p1)) ∨ (((p3 ∨ p4) → ((True ∨ (False → (p1 ∧ (False → p4)))) ∨ (p5 ∨ p1))) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197489293019276450177620765739 : (((False ∧ (p2 → (p1 ∧ p5))) ∧ (p4 ∧ False)) ∨ ((((p4 → (p3 ∨ ((False → p4) → p5))) ∧ p4) → (((p2 → p5) → p5) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317707940517224577417167086996 : (p4 ∨ (((((p1 ∨ (p1 ∨ (True ∨ (False → False)))) ∨ p3) ∧ (p3 ∨ (False ∨ ((p1 → (p4 ∨ p3)) ∧ (p1 ∨ False))))) ∨ (p5 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64747923440308915286035308340 : ((p2 ∨ ((((p2 → ((p2 → True) ∨ (p2 → (p4 ∨ (((p3 → p1) ∨ True) → True))))) ∨ p5) → (((p3 → p5) ∧ True) → p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190819642223728211417884653607 : (((p5 ∧ (((p1 ∧ p3) ∨ True) ∨ p5)) ∨ (False ∧ p5)) ∨ ((False → True) → (((p1 ∧ p2) ∧ ((p3 ∨ True) → p2)) → (False → (False ∧ p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683337726733931001317080608455 : ((((p4 ∨ (((p1 ∨ p3) ∧ ((p4 ∨ p5) ∧ ((True ∨ p5) ∧ p2))) ∨ ((True → False) ∨ False))) ∧ (((p3 ∧ p5) ∨ (p2 → p1)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328899064892198825835404001153 : (True → ((p2 ∨ ((p1 ∨ (p4 ∧ (False ∧ p1))) ∨ p1)) ∨ (((True → p2) ∨ p5) → ((p4 ∨ True) ∨ ((p4 ∧ p5) ∧ ((p2 → p1) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261297352120924710647858699142 : ((p5 → True) → (False ∨ ((False ∨ p1) ∨ ((p2 ∧ (p1 → (p2 ∧ p1))) → ((p4 ∧ p3) ∨ ((((False ∧ False) → p3) ∨ (p5 ∨ False)) → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140909897292388587344181392612 : ((((((False → p5) ∨ False) → p4) → ((True → False) ∧ p4)) ∧ (((False ∧ (p3 ∨ (False → p5))) → p1) ∨ (p3 ∧ p5))) → ((p3 ∨ p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951507427667192538832713053828 : ((((True → (p1 ∨ False)) ∧ (((p1 ∧ (True ∧ (False ∧ p4))) ∨ (p3 → True)) ∧ (True ∧ (((p2 ∧ (p1 → (p1 ∨ True))) → True) ∧ p4)))) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157230274980888324469343764909 : (((((((((p3 → p3) ∨ p1) ∨ p3) ∧ p3) ∧ p1) → p4) ∨ (p3 ∧ ((p1 → p3) ∧ p5))) → p2) ∨ (False → ((p2 ∨ (True ∧ p2)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114413281325044740354902907481 : (((((False ∧ p5) → False) → ((p2 ∧ p2) → ((True ∨ (p1 → p2)) → (p1 ∨ (p4 → p1))))) ∨ (p4 ∨ ((True ∧ False) → True))) ∨ (p5 ∧ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184451590052404272640488780858 : (((False ∨ ((p3 ∨ p2) ∨ ((p1 → p1) → p2))) ∧ (True → p2)) ∨ (((True ∨ (p1 → (p1 ∧ True))) ∧ (((p2 ∨ p2) ∧ False) ∧ True)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165561631033211493421250344845 : (((p2 → (p2 → ((p4 ∨ (p4 ∧ p5)) ∧ p4))) ∧ (p5 ∨ ((p3 ∧ p1) ∨ (p5 → True)))) ∨ (p3 → (p5 ∨ (p1 → (p3 → (p4 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150641864305881235451671753605 : (((False ∨ (((((p4 ∨ (p1 ∧ ((p5 ∧ (p2 → (False ∨ p1))) → True))) → False) ∨ True) → False) ∧ p3)) ∧ p3) → ((p1 → False) ∧ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (((p4 ∨ (p1 ∧ ((p5 ∧ (p2 → (False ∨ p1))) → True))) → False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
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
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (((p4 ∨ (p1 ∧ ((p5 ∧ (p2 → (False ∨ p1))) → True))) → False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338950659509043473886023852014 : (p1 → ((True → p1) → (((p3 ∨ ((False → p5) → ((False ∨ p3) ∨ False))) ∧ (p2 ∧ ((p4 ∨ (False ∧ p4)) ∧ p1))) ∨ (True ∨ (p5 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40975567591746703583933030544 : (((((p2 ∨ p1) ∧ ((p3 ∨ p1) → ((True ∧ ((True ∨ (p2 ∨ p1)) ∧ ((p2 → p3) ∨ (p2 ∧ p5)))) ∧ p3))) ∨ (True ∨ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52660721355507088635817427994 : (((p3 ∧ (p4 ∧ (p5 ∧ ((((p3 ∨ (p4 ∨ p5)) → False) ∨ p4) → p3)))) ∨ ((True ∨ ((p2 ∧ (p3 ∧ (p4 ∨ p3))) → p4)) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62949305462580162664342806698 : ((p4 ∧ (p5 ∧ ((((False ∧ p1) ∨ (False ∧ p5)) ∧ False) ∧ ((False ∨ p3) ∨ (p3 ∧ (((False ∨ p3) → p5) ∨ ((p3 ∨ p1) ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245297114195177967950690536690 : ((p2 ∧ p2) ∨ ((((((p5 → (p1 → False)) ∧ (((p3 ∨ (False ∧ True)) ∨ p4) ∨ (p3 → p3))) ∨ p3) → p4) ∧ True) ∨ (False → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116711381178647446898258562510 : (((p1 ∧ p4) ∨ ((True ∧ p4) ∨ (p2 ∨ (p1 ∨ (((p1 ∨ (True ∧ p1)) ∨ p1) ∨ (((p4 ∨ p2) ∨ p1) → (False → p4))))))) ∨ (p4 ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612690584858410013235670827129 : ((((((p2 ∧ (p3 → (p1 ∨ ((p1 ∨ ((True ∧ p4) ∧ p2)) ∧ p2)))) ∨ ((p4 ∨ (p4 ∨ (p2 ∨ False))) ∨ p4)) ∨ (False → p2)) ∨ p2) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229723079575320563859193896418 : ((p4 → (p4 ∧ False)) ∨ ((((((False ∧ ((((p2 → False) ∧ p1) ∨ (True ∨ p5)) ∧ False)) ∨ p1) ∧ p3) ∨ (False → (True ∨ True))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774736277435874723440627666776 : (((False ∨ (((False → (p4 ∨ False)) ∨ (p1 ∨ (p5 ∨ p4))) → (((p2 ∨ p5) ∧ ((False ∧ (p5 → (p2 ∨ False))) ∨ p4)) → (p1 ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184473169793164164306054375114 : ((((((p2 ∨ (p3 → p5)) ∧ False) ∨ p4) ∨ p3) ∨ (p2 ∧ p1)) ∨ ((((((p3 ∧ p3) ∨ p5) → p1) ∧ p5) ∨ p4) → (p3 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597531346267625836875132022167 : (((((p2 ∨ ((False → p1) → p4)) ∨ (((p4 ∨ ((((p5 ∨ p4) ∧ p1) ∨ p5) → True)) ∨ (p1 ∧ (True ∧ p5))) → (p5 ∨ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201145501561447479337721211444 : ((False → (((p3 → True) ∧ False) ∨ (False → p5))) → (((p4 → (True ∨ (False ∧ p3))) → True) ∧ (((p2 ∨ (p3 → p4)) → p5) ∨ (False → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351017642794661009338754959157 : (p4 → ((p3 → (p2 ∨ (((p3 ∨ (((p3 ∧ p2) ∧ (p1 ∧ (True ∧ ((p3 ∨ True) ∧ p3)))) → (p5 → p1))) ∧ p3) → p2))) ∨ (True → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43276130243443547486790813689 : (((((((p4 ∧ ((((((p5 → p2) ∨ p3) → p1) ∧ p2) ∨ (False ∧ (False ∨ p4))) ∧ p3)) ∧ (p2 → p2)) ∨ True) ∧ p3) ∨ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157529805037907176585288983086 : ((((((False ∧ p3) ∨ (((p4 ∧ (p4 → (p1 → p2))) ∨ p4) → True)) → p1) ∧ True) → (p3 ∨ p2)) ∨ (((p3 → False) ∨ (p3 → p3)) ∨ p2)) := by
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
theorem thm_5_vars_49329744956313085603798290881 : (((p5 ∨ ((((p1 → False) ∧ (((p4 → True) → (((p2 ∨ p2) → p5) ∨ p3)) → p1)) → (p5 ∧ True)) ∨ p2)) ∨ ((p2 → False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47363441534769764592219552085 : ((((p3 ∨ p3) ∨ ((p4 ∧ p5) ∨ (((((p1 → False) ∧ (p3 → p4)) ∨ (True ∨ (p3 ∧ (True ∨ False)))) → False) → p2))) ∨ (p2 ∧ p3)) ∨ p4) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → False) ∧ (p3 → p4)) ∨ (True ∨ (p3 ∧ (True ∨ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202010356102893500961230948783 : (((((p4 ∧ p2) ∧ False) ∧ False) → p1) ∧ (p5 ∨ ((p4 ∧ ((p4 → p3) → ((((p1 ∨ p5) ∨ False) ∧ (p5 ∧ p5)) ∨ p5))) ∨ (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191297869307194524101136176190 : (((p1 → p1) ∧ ((p5 ∨ ((p4 ∨ p3) ∨ p5)) ∧ p3)) ∨ ((((p3 → (p1 ∨ p1)) ∧ p5) ∧ False) ∨ ((p1 → ((True ∨ False) ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302062313061773761580353436100 : (False ∨ (True ∧ (p3 → ((p4 ∧ ((False ∧ ((p5 ∨ (p4 ∨ p1)) ∨ (p3 → ((p2 → p1) ∨ False)))) ∧ (p2 → (p4 ∧ p5)))) ∨ (p1 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254816735883749757761633172156 : ((p3 ∧ p5) → ((((((p1 → ((p1 ∧ (p2 ∧ p3)) → p4)) ∧ p2) ∧ True) ∧ ((p4 ∨ False) → (p1 ∨ (p4 ∨ p1)))) → (p1 ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_69049497519403234025664491929 : ((p5 → (((p5 ∨ p5) → ((p2 ∧ ((p4 ∨ (p5 → False)) → p4)) ∧ ((p1 → (p3 ∧ p1)) ∨ (p4 → ((p2 ∧ p3) → p1))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355617857488668895751268654218 : (p5 → ((p3 ∧ ((((p4 ∨ p1) ∨ p4) → (((((((p4 → True) ∨ True) ∨ p3) ∨ p1) ∨ False) ∧ p5) ∨ p4)) → (p3 → p1))) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316634085059774586485695042527 : (p3 ∨ (p4 ∨ ((p5 ∧ (p1 ∧ (False ∧ ((p1 → p1) ∧ p3)))) ∨ (True ∨ (p4 ∧ (p5 ∧ ((p4 ∨ (False ∧ ((False ∨ p1) → p2))) ∧ False))))))) := by
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
theorem thm_5_vars_134470424363644767913127825586 : ((((p4 ∧ (p1 → (((False ∧ (p5 ∧ p3)) ∧ ((False ∧ (p2 ∨ p4)) ∧ p1)) ∧ (p3 ∨ (p4 ∧ True))))) ∧ True) → p2) ∨ (True ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143366314785769028682378493991 : ((p5 → ((((False → (p2 ∧ (True → p5))) → p1) ∨ ((p1 → p4) ∧ ((p4 ∨ (p1 → (False ∧ p4))) ∨ p4))) ∧ p1)) → ((p2 ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351243728596185505439787805497 : (p4 → (((((p1 ∨ p4) → False) → p2) → ((((p1 ∨ p3) ∨ True) ∧ (p4 ∧ p1)) ∧ (((p5 ∧ p5) ∨ p2) → p3))) ∨ (p1 ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_137760669419579622675687722196 : ((p2 ∨ ((p4 → (((p3 ∨ ((p5 → (False ∨ ((p4 → p3) → p3))) ∧ (p5 ∧ (p5 ∨ p3)))) ∨ p2) ∧ False)) → p4)) ∨ (p5 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617803463176336042664499351561 : (((((((False → True) ∨ (p2 ∨ p1)) ∧ p3) → (((True ∧ True) ∧ (((p1 → (p5 → (p3 → False))) ∨ True) ∨ p1)) ∨ (False ∧ p4))) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
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
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49214238696307310405673020726 : ((((p5 ∧ False) ∧ (((p5 → ((p2 ∧ (((p2 ∧ ((p2 → False) → True)) → True) ∨ p2)) ∨ p2)) ∨ p4) → p2)) ∨ ((False → True) ∨ p5)) ∨ p3) := by
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
theorem thm_5_vars_51526695424408245323263467304 : ((((p5 ∧ True) → (((p5 → False) ∧ ((p3 ∨ p2) ∨ p2)) ∨ ((p5 ∧ p5) → (p2 → False)))) → (((p4 → p2) ∨ (p2 ∧ p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261027191938917321295781650728 : ((p4 → p2) → ((((((p1 ∨ p4) → p5) ∧ False) → (((((p4 ∧ True) ∧ p2) ∨ p4) → (False ∨ p4)) → False)) → False) → (p3 ∧ (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∨ p4) → p5) ∧ False) → (((((p4 ∧ True) ∧ p2) ∨ p4) → (False ∨ p4)) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : ((((p1 ∨ p4) → p5) ∧ False) → (((((p4 ∧ True) ∧ p2) ∨ p4) → (False ∨ p4)) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h9
  -- False on the left can always be used.
  apply False.elim h14
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h15 : ((((p1 ∨ p4) → p5) ∧ False) → (((((p4 ∧ True) ∧ p2) ∨ p4) → (False ∨ p4)) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- False on the left can always be used.
    apply False.elim h19
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h15
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37168995516840311687048898797 : (((((((p5 → p5) → ((False ∧ ((p4 ∨ p1) ∨ p1)) ∨ (False → False))) ∧ p5) ∨ (((p2 ∧ p2) ∨ p3) ∧ (p1 ∧ p4))) ∧ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63207198044019738994348018200 : ((p5 ∧ (((p4 → ((p1 ∨ (p4 → p1)) ∨ p1)) ∧ (p4 → (p3 ∨ (p3 ∧ ((False → p1) ∧ False))))) ∨ ((False ∧ p2) ∨ (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135292259362494560905212943927 : ((((((p1 → p5) ∧ ((p4 → (p4 → True)) ∨ (True → (p5 → (False ∧ p1))))) ∨ p3) ∧ p2) ∧ (False ∧ (p4 ∨ p5))) ∨ (False ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147437163307323715931143348902 : ((((p5 ∧ p1) ∧ (((p3 ∧ p2) ∧ (((False ∨ p2) ∧ (p4 → ((p3 → False) → p1))) ∧ True)) ∧ False)) ∨ p5) ∨ (p1 → ((p5 ∧ False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579220077006875629426149129914 : (((p3 → (p3 → (((((((p4 ∨ p4) → False) ∨ p4) ∨ (True ∨ (((p3 ∧ p3) ∧ p3) ∧ (p3 ∧ p4)))) → False) ∧ (p1 → True)) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119523243787710089504041334204 : ((p5 → (((p4 ∨ p4) ∧ ((True → True) ∨ ((p3 ∨ (p5 → ((True ∧ p5) ∧ ((True ∧ True) → p5)))) → (p1 ∨ p3)))) ∨ p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690555849464376692635674421201 : (((((((p2 → (((p2 ∧ False) ∧ ((False ∨ False) ∨ True)) ∨ p1)) ∧ p4) ∧ p4) ∨ p4) → ((False ∧ (p3 ∧ (p5 ∧ (p4 ∧ False)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779947523635769312168871767388 : (((p2 ∨ (((((False ∨ (True ∧ p3)) ∧ (p2 ∧ p5)) ∧ p5) → ((p1 ∨ (False ∧ (True → True))) ∨ (p5 → (p4 ∧ p2)))) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217933212090660613170123729607 : (((True ∧ p2) ∧ (p5 ∧ True)) → ((p4 ∨ ((p4 ∧ (False → (((p2 ∨ (p2 → p2)) ∧ p1) → ((p3 ∨ (p4 ∧ p1)) ∨ p2)))) → p1)) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357489470363806859516780319047 : (p5 → (True ∧ ((((p3 ∧ True) → p1) → (((p3 → ((p4 → (((p5 → (True ∨ p4)) ∧ True) ∨ p1)) → p4)) ∨ p5) ∨ (p2 ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230457553742959243625764243136 : (((p5 ∨ p1) ∧ p4) → ((p2 ∧ (p5 → (((False ∨ ((True ∨ False) ∧ False)) ∧ p5) ∧ (p5 ∨ (p3 → p3))))) ∨ ((p1 ∧ (p4 ∧ p5)) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548659403285936648330000256 : ((((((p2 ∧ True) ∧ p5) ∨ p1) ∨ (((True → (False ∨ (((p5 → False) → ((p3 → p1) ∧ p3)) ∧ p5))) → p3) → p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48709750076102314892434233947 : ((((False → (p4 → (p2 ∧ (False ∨ p5)))) → ((True ∧ ((False ∨ (p4 → (p3 → p5))) ∧ p5)) ∧ (False → p2))) ∧ (p4 ∧ (p5 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698855402418696939334353244740 : ((((False ∧ (((True → p4) ∧ (p4 ∧ p2)) ∧ (True ∧ (p1 ∨ p2)))) ∨ (((p3 ∧ (False → False)) → (((p5 ∧ False) ∨ True) ∨ p3)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258289536819146272863696431480 : ((p5 ∨ True) → (((((((False → p2) ∧ ((p3 ∨ ((p4 ∧ (p5 ∨ p1)) ∧ False)) → (p4 ∧ True))) → p1) ∨ p3) → p5) → p2) ∨ (True ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262471880132191173907902315597 : (True ∧ ((p4 ∨ (((((((False → (p2 → p2)) → p3) ∨ p5) ∨ ((p5 → False) ∨ (p1 → p3))) → ((p2 → p5) → False)) → p3) ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159923244844378040957515935198 : ((((((p3 → (True → True)) → ((True ∧ p3) ∧ (p1 ∨ True))) → ((p5 ∨ p4) ∧ False)) → True) → p3) → ((p5 ∨ (p3 ∧ True)) ∨ (p1 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → (True → True)) → ((True ∧ p3) ∧ (p1 ∨ True))) → ((p5 ∨ p4) ∧ False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215411794338668097699540157097 : ((p2 ∧ (p3 → (p2 → p5))) ∨ ((((p5 ∨ (p1 ∧ p1)) ∨ (((p1 → True) → (p4 → (p1 ∨ True))) → False)) ∧ (True ∨ (p5 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51275975272095020922970341329 : (((False ∧ ((p4 → ((True ∧ True) → True)) → ((p2 → ((p5 ∧ p5) ∨ (p4 ∧ True))) ∧ p3))) ∨ (((True ∧ (p2 → p2)) → p3) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809384847097472867456514576318 : (((p5 → ((p4 → ((p5 → p2) → (p4 → ((((p5 ∧ ((p4 → p4) ∧ True)) ∧ ((False → (False ∨ p5)) ∨ True)) → p3) ∨ p3)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196920215417585589963505779678 : (((((p4 ∨ True) ∧ (False → p5)) ∧ False) ∨ p4) ∨ (((True → ((p2 ∧ p3) → (p1 → (((p1 ∧ True) ∧ False) ∧ p5)))) ∧ (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125000208028237261639176844165 : ((((False → p4) ∧ p4) ∧ ((True ∨ ((False → p5) ∧ (((True → p4) → (p1 ∧ (True ∧ False))) ∨ (p2 ∨ (True → p5))))) → True)) → (p4 → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112044611109628766601523979880 : (((((True ∨ p1) → p3) → (p2 ∧ (p1 ∧ (((p4 ∧ p4) ∨ p3) ∧ (p4 ∧ ((((False → p5) ∧ p1) ∨ p5) ∨ p5)))))) ∨ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57330700412041889776134893689 : (((p1 ∧ (p4 ∧ p1)) ∨ ((p2 ∧ (p4 ∧ ((((p5 ∧ p2) ∨ (p2 → p1)) ∨ (True → p2)) → p4))) → (False ∨ ((True → p5) ∨ True)))) ∨ False) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659044061449884870009954544974 : ((((p2 → ((((True ∨ False) ∨ p2) → ((True ∧ ((p2 ∨ (p1 ∨ (p3 ∨ (False → (p3 → p4))))) ∨ True)) → False)) ∧ p1)) ∨ (False → p2)) ∨ p1) ∧ True) := by
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



