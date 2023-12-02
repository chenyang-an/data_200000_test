variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63264433928992416259540594046 : ((p5 ∧ ((p5 ∧ (((p2 ∨ p1) ∨ p2) ∨ p2)) ∧ (((((True ∨ (p1 ∧ ((True ∧ p4) ∨ p3))) → p1) ∨ (p1 ∧ p3)) → p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663857603627307593302563682365 : ((((p3 ∧ (((False ∨ p5) → (((False → ((p5 ∧ p3) → p4)) → p3) → p3)) ∧ ((p4 ∨ (p3 → False)) ∨ (p5 ∨ True)))) → (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61085360387038575049585005484 : ((False ∧ (((p5 ∨ (((p4 → ((True ∨ p2) → p4)) → (p4 → p1)) → (False → False))) ∨ (p2 ∧ p4)) → (((True → p1) → p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718830886733753149889602014267 : (((((p5 ∨ p1) ∨ (p3 ∨ p4)) ∨ ((p4 ∨ ((True ∨ ((p2 ∧ ((p4 ∨ (p4 ∨ (p3 ∧ False))) ∧ p2)) ∨ False)) ∨ (False ∧ p3))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147027712569950640394896296951 : (((((p5 → ((False ∨ True) → ((p1 → ((False ∨ p5) ∧ True)) → p4))) ∨ False) ∨ (True ∧ (True → p3))) ∧ p1) ∨ ((False ∨ p4) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173511573257465196901455023831 : ((((((p1 → p4) ∧ (((False ∧ False) ∨ False) ∧ False)) ∨ p1) → (False ∨ False)) ∧ p5) → (((p3 ∧ (False → (p3 ∨ p3))) ∧ p3) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 → p4) ∧ (((False ∧ False) ∨ False) ∧ False)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356895273224296184568273127198 : (p5 → ((((p1 → p5) ∨ p5) → False) → ((p2 ∨ (p5 ∧ ((p5 ∨ (p1 → p5)) → (True ∧ p1)))) ∨ ((p1 ∧ (p2 → (False ∨ False))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 → p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198607312691979168619184857746 : ((p2 ∨ ((False ∧ p1) ∧ (p5 ∧ (False ∨ False)))) ∨ (((((((p5 ∧ p4) → (p3 ∨ (p1 ∧ p2))) ∧ p3) → p4) → p5) ∧ p4) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749462916379680848381942204306 : (((True ∧ ((((p1 → (((False → (p1 → p1)) → p4) → True)) → p2) → (((p3 → False) ∨ (p5 ∨ p1)) ∨ (p5 ∨ (p5 → True)))) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63402285937034586481903858475 : ((p5 ∧ (p3 ∨ (((p2 → p4) ∨ (p5 ∧ ((False ∨ p3) → (p2 ∧ True)))) ∧ (((p3 → True) ∨ p4) → ((p5 ∨ (p5 → p1)) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226243396933752221832147427021 : (((p3 ∨ p1) ∨ p1) ∨ ((False ∧ ((p2 ∧ (p4 ∨ (p4 ∨ ((p3 ∨ False) ∨ (p5 ∧ p1))))) ∨ ((p2 ∧ p2) → p2))) ∨ (p2 → (p4 ∨ p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180171403924719318538054254309 : (((((p1 → (p1 → p2)) ∨ (p5 ∧ False)) ∨ (p3 ∧ (True ∧ p1))) → p1) → (p2 ∨ ((((p2 ∨ p1) ∨ ((p3 → p3) ∧ p4)) → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 → (p1 → p2)) ∨ (p5 ∧ False)) ∨ (p3 ∧ (True ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∨ p1) ∨ ((p3 → p3) ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : ((p2 ∨ p1) ∨ ((p3 → p3) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171357229961382415625286782565 : (((((p1 ∨ (p3 ∨ ((p2 ∨ (False ∧ p3)) ∧ p3))) → False) ∧ (p2 ∨ p1)) ∧ p3) ∨ (((p1 ∧ p1) → p4) → ((False ∧ p1) → (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216732548904926945558733414944 : ((((p2 ∨ p3) → True) ∧ p4) → (p4 ∧ ((p1 ∨ (p3 → p4)) ∧ (((True → ((p5 ∨ p3) → False)) ∨ True) ∨ ((True ∧ True) → (False ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114790549144519757755387605796 : ((((((((True ∨ p2) ∨ False) ∧ p1) → (p1 → p4)) → True) ∧ (p3 ∨ p3)) ∧ ((True ∧ (True ∨ ((p1 ∨ p5) ∧ p1))) → p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345448454422141046683388344450 : (p3 → ((((p2 ∨ p3) → (p2 ∧ ((p1 → (p2 ∧ p5)) → (((p4 ∧ (False ∧ (p1 ∨ (p2 ∨ p1)))) ∨ p4) ∧ p5)))) ∨ (False → p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245842413650841040546448110867 : ((p3 ∧ p4) ∨ ((p3 ∧ ((((p2 ∧ (((p2 → p1) ∨ (False → p5)) → (p5 → (False → (False ∧ p2))))) ∨ p4) ∧ p5) ∧ p2)) → (p1 ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158113190291839587679828492882 : (((True ∧ (p4 ∨ (p3 ∧ p3))) ∧ (p2 ∨ ((p5 → (p3 → (((p2 → p2) ∨ p5) ∨ False))) → p4))) ∨ (p2 → (p1 → ((p5 ∨ p1) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605187578783324120442912546934 : ((((p2 → (((p5 → p3) → p3) → (((p5 ∧ p5) ∧ ((((False → p4) → (p2 ∧ (p1 ∨ p3))) → True) ∧ p1)) ∨ (p1 ∨ p3)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663171075303132412018691410071 : (((((False → p4) ∧ ((((True ∨ (p3 → p4)) ∧ (True → p5)) → False) ∨ ((p4 ∧ (True ∧ False)) ∧ ((False ∨ p5) → p3)))) → (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696316652143297233201157177684 : ((((p2 → (((p2 ∧ (True ∧ False)) → (p1 ∧ ((p5 ∧ p2) ∧ p4))) ∧ True)) → ((p4 ∨ (((p5 ∨ p2) ∧ (p1 ∨ p5)) → p2)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663165414414728684488655208072 : (((((False → True) ∧ (((p5 ∨ ((p4 → (p2 → p2)) → (p3 ∧ p3))) ∧ (False → ((p1 ∧ p5) ∨ (False ∧ p4)))) ∧ p3)) → (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47193536318692417172706784563 : (((((p3 ∨ ((p2 → False) ∨ p4)) → (((True ∧ True) ∧ True) → False)) ∨ (False ∨ (False → (p1 ∧ ((p1 ∨ p1) ∧ p4))))) ∨ (p4 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690923921204218894487787608809 : ((((((((p1 ∨ p5) → (((p1 ∨ True) ∨ p4) ∨ True)) → p2) → p4) ∨ (p1 ∨ p4)) → (((p1 ∧ (p1 → (p5 ∧ p5))) ∧ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18053156392577217268725600512 : (((p1 ∧ (False ∧ (p5 ∧ (p3 → ((p3 → ((False ∨ p5) ∧ ((True ∨ True) ∨ (p5 → p1)))) → False))))) ∨ (((p5 ∧ p3) ∨ p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64929858641025991841834619517 : ((p2 ∨ ((((p4 ∨ (p4 → True)) ∨ p5) ∧ (p3 ∧ (((p2 → p4) ∧ True) ∧ p1))) ∨ ((p4 ∨ ((p3 ∧ False) ∨ (True ∧ True))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115169057820464442376041607328 : ((((((p2 → p4) ∨ (True ∨ True)) → (p3 → p2)) ∨ p2) ∧ (p2 ∨ (p5 → (((p4 ∨ (False → (False ∨ p4))) ∧ True) ∨ p3)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53046823100773579478218287043 : ((((p2 → p4) ∧ (p2 → (((p3 → p4) → p2) ∧ (False ∧ p1)))) ∧ ((p4 → ((True ∧ p5) ∧ (p3 → ((p1 → p2) ∧ p4)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806821320276578365779660927987 : (((p4 → (((False → p4) → (((p4 → True) ∧ p2) ∧ (((p2 → (p4 → p2)) ∨ (((p1 ∨ p1) ∧ p1) ∨ p2)) ∧ p3))) ∨ (p5 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184062318275461151312068990396 : ((((((p5 ∨ p5) ∨ p2) ∧ (p1 → p4)) → (p2 ∧ p4)) ∨ p4) ∨ ((False → ((True → (p3 ∨ ((p1 ∨ p3) → p4))) → False)) ∧ (False → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305695438880358481176066481278 : (p1 ∨ ((((p5 ∧ ((p1 → p3) ∧ (p3 ∨ False))) → p1) ∧ p4) → (((p3 ∨ ((p5 ∧ p4) ∨ (p3 → p2))) ∨ ((p3 ∧ p1) ∧ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258038547450816433215964853991 : ((p4 ∨ p2) → ((p5 ∨ ((p1 → p3) → (((((True → p4) ∨ False) ∨ (p1 ∨ p5)) ∨ p2) ∨ (((p2 ∨ p5) → False) → (p2 ∨ p1))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41677857548729641028601850006 : (((((p2 ∨ p2) ∧ ((p4 → True) → p2)) ∨ (((p1 ∨ p4) ∨ False) ∨ ((p1 ∧ True) → ((False → ((p2 ∧ False) ∧ p2)) ∨ p1)))) ∨ p2) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764863560869713275985338801463 : (((p4 ∧ (((False ∧ (True → ((p3 → (((True → p2) → p3) → ((p4 ∧ p2) ∨ (p3 → False)))) ∧ False))) → ((p2 ∧ True) ∧ True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244135581256720172060004078541 : ((True ∧ p4) ∨ (((p3 ∨ (p2 → True)) → ((((False ∨ (p3 ∨ p1)) ∨ True) → ((p4 → (p2 → (p2 ∨ (True ∧ p4)))) ∧ p5)) ∧ False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777893930044125116661729582390 : (((p1 ∨ (((p4 ∧ p1) ∧ p1) ∧ ((((p4 → p5) ∨ (((p1 ∨ ((True ∨ p4) → (p5 → (p1 ∧ True)))) ∨ p3) ∧ p4)) → p2) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233436241832104755111924243927 : ((False ∨ (True → p2)) → ((((p1 ∨ ((p4 → p3) ∧ p5)) ∨ False) ∧ (p3 ∨ (p2 → p3))) ∨ ((True → (((p2 → p4) → p2) ∨ p4)) ∨ p1))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111501085723927934236793359142 : (((p4 → (((p5 → True) ∧ (p2 ∨ ((p5 ∧ (((p3 ∧ (p2 ∨ True)) → (False ∧ (p5 ∧ p3))) ∧ False)) ∨ p1))) ∧ False)) ∧ p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327244225154342676673097725099 : (True → ((p5 → (p2 → ((p1 ∧ (((p5 ∨ p4) ∨ p4) ∨ ((((False ∨ ((p5 ∧ p4) ∨ p3)) → p1) ∧ (p1 ∨ False)) ∨ p3))) → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339665724124924319132263833321 : (p1 → (p3 ∨ (((p1 ∨ p1) → ((p2 ∨ (p3 ∧ (((((p2 ∧ (p2 ∧ p3)) ∨ p2) ∨ (p4 ∨ (p2 ∧ True))) ∨ p4) → False))) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134904095398134307795960703653 : (((((p4 ∨ (((True ∧ p2) ∨ ((p4 ∧ p2) ∨ p5)) ∨ True)) ∧ (p4 ∧ ((False ∧ p5) → p1))) ∧ p1) ∧ (p1 ∧ True)) ∨ (True ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130420361100893272460491524102 : ((((p2 → (True ∧ (p5 ∧ (False ∨ ((p4 ∨ (p5 ∧ (p5 ∨ p2))) → (p1 ∧ p2)))))) ∨ True) ∨ ((p4 → True) ∧ p4)) ∧ (p2 → (p2 ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684529982867733698812488098811 : (((((False ∨ (p4 ∨ (p1 → (False ∨ p4)))) → ((((True ∧ (p3 ∨ p5)) ∨ p2) ∧ True) ∧ p4)) ∨ ((p4 ∧ p2) → (p3 ∨ (p4 ∧ p4)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729936555316248917203685680695 : (((((p4 ∧ True) → p5) → (((((((((p3 ∨ True) ∧ (p5 → p3)) ∧ p2) ∨ (p3 ∧ p4)) ∨ p2) ∨ True) ∨ p3) → p2) ∨ (True → True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323213429290696699784869643914 : (p5 ∨ (((p5 ∧ ((p2 → p5) → ((True ∨ ((((p4 ∨ p3) → p2) → p3) ∨ p1)) → p4))) ∧ ((True → True) ∧ (True → p2))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90061326083912401768019802329 : ((((p1 ∧ p1) → True) → ((((((True ∨ p3) → (p1 ∧ (True → False))) ∨ True) ∨ ((False ∧ p5) ∨ ((False → p1) ∧ True))) → p5) ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_552936208604244181210368389368 : (((p2 ∨ (((((((False ∨ p3) ∧ p1) ∨ (p4 → (False → p4))) → False) ∧ (p3 → (p5 ∨ (p5 → p3)))) → ((True ∨ p2) ∧ p5)) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∨ p3) ∧ p1) ∨ (p4 → (False → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158239481113117173540235315634 : ((((p4 ∧ p4) ∧ p3) ∨ (((p5 ∧ True) ∨ (((p3 → False) ∨ (p5 → (True ∧ p4))) → p3)) → p5)) ∨ ((p3 ∨ p5) → ((False ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64868410924114685964059079487 : ((p2 ∨ ((p1 ∧ ((((False ∨ p2) ∨ (p4 → ((False → ((p1 ∧ False) → p1)) → p1))) → (p5 → (p1 ∨ False))) → p4)) ∨ (p4 → p4))) ∨ p5) := by
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
theorem thm_5_vars_706730144794657343243155032810 : (((((((p4 → (p1 → p5)) → p4) ∨ p5) ∧ p4) ∨ (p3 ∧ ((p1 → (False → (p2 → (((p4 → False) ∨ (p1 ∧ p3)) ∨ True)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173506931693437842153645114981 : (((((p5 → ((p3 → p3) → p2)) ∧ (p1 ∧ (True ∧ p5))) ∨ (p2 ∧ p4)) ∧ True) → ((True ∧ p3) ∨ ((p2 → (True ∧ p4)) ∨ (p5 ∨ p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227805742298730665763953320770 : ((p2 ∧ (True ∧ False)) ∨ (((((((True ∨ p1) ∧ True) ∧ (p3 ∨ (p3 ∨ ((p1 ∨ False) → True)))) ∧ p2) ∨ True) ∧ (p1 → p1)) ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113774673405763649006699049981 : ((((p5 ∨ ((p1 ∧ p5) ∨ True)) → ((((p2 ∧ (p1 ∨ p4)) ∧ p5) ∨ True) → (p1 → ((p5 → p5) ∧ p2)))) → (p2 ∨ p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165239475690447786863742612909 : (((p2 ∧ (p2 ∨ (True → ((p5 → ((False ∧ False) ∨ p3)) ∧ (p4 ∧ True))))) ∨ (p2 ∨ False)) ∨ (False → (p4 ∧ ((False ∧ p3) ∧ (False ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124027553823581139168078370040 : (((((p1 ∨ True) ∧ ((p4 ∨ p1) → ((False ∧ True) ∧ p3))) ∧ False) → ((True ∧ (((p2 → p2) ∨ False) ∧ (p3 ∨ True))) → p3)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69172865185551086166308189737 : ((p5 → (((True → ((p5 ∨ (p4 ∨ True)) ∧ ((p5 ∧ (p1 ∨ p4)) → (p1 ∧ True)))) ∧ p5) → ((p4 ∨ (True → p1)) ∨ (p5 ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893822339297552866679852237094 : (((((p1 ∧ True) ∨ (((((p3 ∨ p1) ∧ (p2 ∨ p3)) ∧ p5) ∨ (p4 ∨ False)) ∧ (p4 ∨ ((p3 ∧ p3) → False)))) ∧ (True → (p2 ∧ False))) → p3) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h20 =>
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h21 =>
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h22
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h27 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h28 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h29 := h3 h28
            -- We need to get the right conjuct of h29 based on <expert-advice>.
            let h30 := h29.right
            -- False on the left can always be used.
            apply False.elim h30
          case inr h31 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h33 := h3 h32
            -- We need to get the right conjuct of h33 based on <expert-advice>.
            let h34 := h33.right
            -- False on the left can always be used.
            apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h36 =>
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h37 =>
            -- One of the premise coincides with the conclusion.
            exact h35
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h40 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h42 := h3 h41
          -- We need to get the right conjuct of h42 based on <expert-advice>.
          let h43 := h42.right
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h45 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h46 := h3 h45
          -- We need to get the right conjuct of h46 based on <expert-advice>.
          let h47 := h46.right
          -- False on the left can always be used.
          apply False.elim h47
      case inr h48 =>
        -- False on the left can always be used.
        apply False.elim h48
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213317490919401274619713640407 : (((False ∧ (True → True)) ∧ p2) ∨ (((((p4 ∨ p4) ∨ p2) ∧ (p4 ∧ (p5 ∨ ((p2 ∧ p5) → False)))) ∧ p1) ∨ (False → ((False ∨ p2) → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684383055615188985912705084572 : (((((((((p4 ∨ p3) ∧ p1) → p4) ∧ (p1 → p3)) ∧ p5) → ((p4 ∨ True) ∧ (False ∧ p3))) ∨ ((((p5 ∨ True) ∧ p5) → p2) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_135854360347294687867402803055 : ((((p1 ∧ (((p2 ∨ True) → (p3 ∧ False)) ∨ (p1 ∧ p1))) ∧ p3) ∨ (((p5 ∧ p5) ∨ True) → (False → (p3 ∧ p5)))) ∨ ((True ∨ p2) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_259070631416887877390221735162 : ((True → p5) → ((p1 ∨ (((((False ∧ (p1 ∧ False)) ∨ p1) → ((p1 → False) → (False → p4))) ∨ p5) → (p1 → (p2 ∨ (p2 ∨ p4))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209289942346398800588135558283 : ((True → ((p1 → True) ∧ (p1 ∧ False))) → ((False ∨ ((p3 ∧ (((False → ((p2 → p3) ∧ p2)) ∨ p4) ∨ (p2 ∧ False))) → (p4 ∨ True))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338175526946846775483472030577 : (p1 → ((p5 ∧ ((((False ∧ p4) ∨ p3) → p3) ∨ True)) → ((p1 → ((p1 → (p3 → (True ∨ p5))) → ((True ∧ p2) ∧ p2))) ∨ (p1 ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246089328218718345342349444112 : ((p4 ∧ p1) ∨ (((False ∧ (p2 ∨ ((p3 → p2) ∨ p3))) ∨ ((p3 ∨ ((p4 → p4) ∧ (False → p5))) ∧ True)) ∨ (p3 ∧ (False ∧ (p1 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339803676489201586312183675611 : (p1 → (p5 ∨ ((p3 ∨ (((((((p5 → p2) ∧ False) ∧ True) → (p4 ∧ p4)) → p2) → (p1 ∧ p2)) ∧ p2)) → (p4 ∨ ((False ∧ False) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185162213522160447509045008168 : (((p5 ∨ p3) → (True ∧ (False ∨ (p1 ∧ (p3 → (True ∨ p3)))))) ∨ (p2 → ((False ∨ ((p4 ∧ p5) ∧ True)) ∨ ((p4 ∧ (p5 ∧ True)) → p2)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47796114967052202302682557896 : ((((((((p4 ∧ (p1 ∨ ((p4 → (p2 → p1)) ∨ (p5 → p2)))) ∧ (p5 ∧ p5)) ∧ (p1 → p2)) ∨ False) → p2) → p3) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172631321977289234858902278954 : (((p4 ∧ p1) ∧ (((p5 ∧ (((False ∧ p4) ∧ (True → p2)) ∧ p5)) ∨ True) ∧ p3)) ∨ ((False ∧ ((p4 → (p1 ∨ p3)) ∧ p1)) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38427015660432445050795158884 : (((((((((p3 ∨ p5) ∨ (True → p4)) ∨ True) → False) ∨ (True ∨ True)) ∧ True) ∨ ((True ∨ ((True → p5) ∨ (p3 ∧ False))) ∨ p4)) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777504460846134408414285080606 : (((p1 ∨ ((p2 ∨ ((False ∧ (False ∧ p5)) ∧ ((p4 ∨ ((False ∨ True) ∨ p5)) ∧ True))) ∨ (p1 ∨ (((False ∧ p1) ∧ (p3 → p2)) → p3)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149876032529012010706349961979 : ((p2 ∨ ((((p1 → ((False ∨ (((p4 ∧ p4) → p2) → False)) ∧ False)) → False) → p4) ∧ ((p2 → False) → p3))) ∨ (True ∨ ((p2 → p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53799709777384356220052535457 : (((((True → (p1 ∨ p3)) ∨ ((p5 ∧ p2) → True)) → p3) ∨ ((p4 ∧ p5) → (((False ∧ (p3 → p4)) → ((p1 ∧ p1) ∧ False)) → True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324161395381124979001853864413 : (p5 ∨ (((((p5 ∧ False) ∨ False) ∨ (p1 ∧ (p4 → True))) ∨ True) ∨ ((p1 ∨ False) ∨ ((p3 ∨ (p2 ∨ False)) ∨ ((False ∧ p2) ∨ (p4 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680636024452063827673843937921 : (((((p4 → (((p5 ∨ p2) ∧ p3) ∨ True)) ∧ ((p3 ∨ (False ∨ p3)) ∨ (((True → p5) ∧ True) ∧ p2))) → (((p4 → p3) ∧ p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112472199134931503888136634749 : ((((((p1 ∨ p5) → p5) ∧ ((p2 ∨ (False ∧ p4)) → (p4 → ((p3 ∨ p2) ∧ (True ∧ ((p1 ∨ p1) ∨ p4)))))) ∨ p1) → p2) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703076356801271062100930529496 : (((((p2 ∧ False) ∨ ((True → p5) ∨ (p1 ∧ (False ∧ False)))) ∨ (((p5 ∨ p3) ∨ (p2 ∨ (True ∧ ((True → p5) ∧ False)))) ∨ (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234387635740702289521193964119 : ((p1 → (False → p3)) → (False ∨ (((p5 ∧ (p5 → (p4 → (p4 ∧ (((p5 → (p2 → (p2 ∨ p3))) ∨ p5) → False))))) ∨ (True → True)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203891550564122545825114815528 : ((p1 → ((p4 ∨ True) ∨ (p3 ∨ p2))) ∧ ((((p3 → (True ∧ (p1 ∨ False))) ∧ p2) ∨ (False ∧ p2)) ∨ (False → ((p5 → (True → p4)) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115248605844651720566637250969 : ((((p3 ∧ (p5 ∨ (True → (False ∨ p3)))) → (False ∨ p5)) ∨ (((((False → (p2 → (p1 → p1))) → p3) ∧ False) ∨ p2) ∨ True)) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47096927585926522891638719337 : ((((((((p4 ∨ ((p4 → p3) → (p5 ∨ True))) ∨ p1) → (True → (True ∨ p4))) → p3) ∧ p2) ∧ ((p5 ∨ p4) ∧ p5)) ∨ (p4 → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55083883690234443304429389178 : (((False → (p1 ∨ (p2 ∧ (p2 → p1)))) ∧ ((True ∧ p5) → (((((p3 → p2) ∧ ((p4 ∧ (False → True)) → p1)) ∨ p2) ∨ p5) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354797266760857383015410219290 : (p5 → ((((p3 → (p1 → (p4 ∧ p1))) → p5) → ((((p2 → (False ∧ p4)) ∨ False) ∧ (((p2 ∧ (p2 ∧ p4)) ∧ p5) ∨ p4)) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202038168219650731925628625926 : ((((True ∨ (p4 ∨ p4)) ∧ True) → True) ∧ ((((False ∧ (False → True)) ∨ p2) ∨ (p1 ∧ (False ∨ (True → ((p2 → False) ∧ (p5 ∨ p3)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328809835476113954408725552677 : (True → ((((((p5 ∨ p1) → False) ∧ (p2 ∨ p5)) ∧ p5) ∧ True) → ((p4 → (((p1 ∨ p2) ∧ (False ∨ p1)) ∧ (p4 ∧ p1))) ∨ (p1 ∨ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : (p5 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164730889213611179040011747588 : ((((p1 ∨ (((p5 ∨ (True ∨ ((p1 ∨ p2) ∨ p1))) ∧ p3) ∨ (p1 → True))) → False) ∨ True) ∨ ((p4 ∨ ((p3 → False) → p3)) → (p2 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198259386891576984989845390492 : ((False ∧ ((False ∧ (p3 ∨ (p2 ∧ p2))) ∨ p2)) ∨ ((False ∧ (p5 ∧ p3)) → ((((((p1 ∨ True) → p4) → p1) ∨ p3) → (p4 ∨ p1)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137920861247094802070666634001 : ((p4 ∨ ((p1 ∨ p1) → (p5 ∧ ((((((p4 → (p5 ∨ p4)) ∨ p4) ∧ p5) ∨ ((p5 ∧ p5) ∧ p2)) ∨ True) → p2)))) ∨ (False → (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669339005156626968175777683905 : ((((((False ∨ ((p2 ∨ True) ∧ p2)) ∨ (p2 ∨ (((p5 → False) ∧ ((p2 ∧ False) → p4)) ∨ True))) ∧ (p1 ∨ p3)) ∨ (True ∨ (p1 ∧ p5))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_347707273549146488216513174752 : (p3 → (((p5 ∧ p5) → p5) ∧ (((p2 ∧ p1) ∨ ((p4 → (p3 → p5)) ∨ (False → False))) ∧ ((((p5 ∧ (p1 → False)) ∨ p3) ∨ False) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264256073369475068797295138040 : (True ∧ (((p3 → (p4 → (p3 ∧ p5))) ∧ False) ∨ (((p4 ∨ p1) ∨ p4) → (((False ∨ (False ∨ (p3 ∨ (False → False)))) ∨ True) ∧ (False → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171979063783269410288304659395 : (((True → (((p1 → (p2 ∨ p4)) → (p3 ∨ (True → p3))) ∨ True)) ∧ (p1 ∨ p3)) ∨ ((((p4 ∧ p5) ∨ ((False ∨ p5) ∧ p2)) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60199659054058508370336688395 : (((p5 ∨ p5) → (((False ∧ (p3 → (False ∧ True))) ∨ ((p4 ∨ p5) ∧ ((p4 → (p1 ∧ (p5 → (False ∧ False)))) ∧ (p3 ∧ p5)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62013019428069972033355012373 : ((p2 ∧ (((True ∨ p1) → True) ∧ (((p2 ∨ (True ∨ p5)) ∧ (p1 ∨ True)) → ((p2 → (p2 → p1)) ∧ ((True → p1) → (p5 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117518342958641787703477071239 : ((p2 ∧ ((p4 ∨ (((True → ((((False → True) ∨ True) → (p5 ∧ p5)) ∨ p2)) ∧ False) ∨ (((p5 → p4) ∧ p4) ∧ p1))) ∨ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137863960853257144293772160039 : ((p3 ∨ (p1 ∨ ((p3 ∧ (((False → (False ∧ p3)) ∧ p1) ∧ ((False ∨ p3) ∧ ((p3 ∧ (p2 ∨ p1)) ∨ p1)))) → False))) ∨ (True → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197621199295477109528443662482 : (((((p2 ∧ p1) → p2) ∧ True) → (p5 ∨ p1)) ∨ (p2 → ((True ∨ ((False ∧ p5) ∨ ((p3 ∧ (p1 → p2)) → True))) ∨ ((p3 ∨ p4) ∨ p5)))) := by
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
theorem thm_5_vars_111400200737791625565239076255 : (((p1 ∨ (True → ((p5 → (p4 ∨ ((((p2 ∧ (p3 → p1)) ∧ False) ∨ ((False → p2) ∧ (p5 ∨ False))) ∨ p5))) ∨ p3))) ∧ True) ∨ (p3 → p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156982178587090224825817443212 : ((((((p3 → (p5 ∧ p4)) → False) → (False ∧ p5)) → ((p4 ∧ (p4 ∨ (p4 → True))) → p2)) ∨ True) ∨ (False ∨ (p3 → ((False ∧ p2) ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340795534007414921936047336240 : (p2 → ((((p4 → p3) → ((((p3 ∧ ((p5 ∧ (p4 → p2)) → p4)) ∨ ((False ∨ p3) ∨ (p4 ∧ p5))) ∨ (p5 → p2)) ∨ p1)) → p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4387752670915208085816107076 : (p1 → ((((p3 ∧ ((False → (((p3 ∨ p2) → p4) ∧ False)) → (((p5 → True) ∨ False) ∨ (False ∨ (True ∨ p2))))) → p3) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



