variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57750590292041073872993281223 : ((((p1 → True) → p1) → (p1 ∨ ((((p5 ∧ p3) → p3) ∨ p1) → ((p2 ∨ (p4 ∧ (((p3 ∨ p1) ∧ True) ∧ (p2 ∧ p5)))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686040714525846469652808801653 : (((((((False ∨ (((p4 ∧ False) → False) ∨ p4)) ∨ p5) ∧ (False ∨ (False ∧ p2))) → (p4 → True)) → ((p1 → ((p5 → p4) ∧ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_819755362964520579298823828 : ((p3 ∧ ((p5 ∨ (True → p4)) → (((True → (p1 ∧ p1)) → (p5 ∨ (((True ∨ p2) ∧ (p2 ∨ p1)) ∧ (False ∧ p5)))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301358924448294403655902145096 : (False ∨ ((((p3 ∧ p4) ∨ p3) ∧ p1) ∨ (((True ∨ p4) → ((p1 → ((p4 ∧ p5) → (True ∧ (p3 ∧ False)))) ∧ (p4 → (True ∨ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55620512379425741378926154020 : (((p3 → (p1 ∨ (True ∨ (True ∨ p1)))) → (True → (p1 ∨ (((((p1 → (p4 ∧ (p1 ∨ True))) ∧ (p4 ∧ True)) ∨ p1) ∨ False) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342144707582416119128051285529 : (p2 → (((((p1 ∨ (p1 ∧ (p5 ∨ p2))) ∨ (p4 ∨ p3)) ∨ (((p2 ∧ p4) ∧ (p4 ∧ False)) → p5)) ∨ False) ∨ ((p5 ∧ (p3 → p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149521929517900313109365824746 : ((p1 ∧ (p4 ∧ (p4 ∧ (((p4 ∨ (p5 → p4)) ∨ p4) ∨ (((((p3 ∨ p5) ∨ False) → True) ∨ p4) ∨ p4))))) ∨ (((p3 ∨ True) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312101318187637233221330040684 : (p2 ∨ (True → (((((((p3 ∨ (p2 ∨ ((True ∧ False) ∧ (True → p2)))) ∨ p5) → True) ∨ p1) → ((p2 ∨ (p5 ∨ p2)) ∧ p1)) → p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p3 ∨ (p2 ∨ ((True ∧ False) ∧ (True → p2)))) ∨ p5) → True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10242279214180649801586050637 : (((p2 ∨ (p5 → ((False ∧ (False → True)) ∨ ((p1 ∨ ((True ∧ p5) → ((p2 ∧ p4) → (p3 ∨ p5)))) ∧ ((p4 ∨ False) ∨ p5))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190936791793315065836718263100 : ((((p2 ∧ p4) ∧ (p1 → False)) ∧ (True → (False ∧ False))) ∨ ((False → p1) ∧ ((((True ∨ ((False ∨ p2) ∨ (True → False))) ∨ False) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_781218172325879087934741514313 : (((p2 ∨ ((p2 → p4) → ((p3 ∧ ((((p5 ∨ p2) ∨ (p3 → (p5 ∨ (p1 ∧ p4)))) ∧ p4) ∨ ((p4 ∧ (p2 → p1)) ∨ True))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147506711436041671540411741483 : (((p2 ∨ (((p3 → p3) ∧ ((p5 ∨ (p1 ∨ (((False ∧ (True ∨ p2)) ∨ p3) ∨ p5))) ∨ p4)) ∨ True)) ∨ p1) ∨ (p4 → ((False → p3) ∨ p4))) := by
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
theorem thm_5_vars_61163626104629041349720985922 : ((False ∧ ((True ∧ (p5 → p2)) ∧ ((False ∨ (p2 ∧ (False ∨ (False ∨ ((p5 → p3) → p1))))) → (p5 ∧ (p1 ∧ (p4 → (p3 → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46837480845653149410083294041 : (((((p1 ∧ (((p5 ∧ p3) ∨ p1) ∨ (p1 ∧ (False → p1)))) ∨ (False ∨ ((False ∧ (p4 ∨ p1)) ∧ (p1 → p3)))) ∧ p2) ∨ (p4 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63955444286057073996149300559 : ((False ∨ ((p5 ∨ (((((False → p2) ∨ p4) ∧ (((p2 ∧ False) ∧ (p2 ∨ (True → False))) ∧ p4)) ∧ ((p1 ∧ True) ∧ p4)) ∨ True)) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_258789727350869059166633392971 : ((True → False) → (((p1 ∨ ((p4 ∨ p3) ∨ p2)) ∨ p4) ∧ (((p3 ∨ p1) ∧ (p2 → (((p4 ∨ p4) ∧ ((p5 → False) → p4)) → p3))) ∧ p4))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64309457744007297694157861681 : ((p1 ∨ (((p2 → ((p4 ∧ (p2 → (True → (((False ∧ True) ∨ p5) ∧ p5)))) ∧ ((True ∨ (True ∨ (p2 → p3))) ∨ p4))) ∧ p4) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233743634573547255184105676511 : ((p3 ∨ (p5 ∧ False)) → (((p3 → ((((p2 ∨ p5) ∧ p3) ∧ ((p5 ∧ p4) → True)) ∧ p4)) ∨ (((p5 ∧ p3) → p5) → (p1 ∨ False))) ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158249512785926556318275620823 : ((((p5 ∨ False) ∨ False) ∨ (((p1 → False) → (False ∧ (p1 ∧ p5))) ∨ (((p3 ∧ p1) → False) → True))) ∨ ((False ∧ p5) → ((True ∧ False) ∨ True))) := by
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
theorem thm_5_vars_154771736777918131240726187413 : (((p4 ∨ (((p3 → True) → p4) ∨ ((p5 ∧ p2) ∨ (((p1 → p1) ∨ False) ∨ True)))) ∨ (True ∨ False)) ∧ (p2 → (p2 ∨ (p2 → (p1 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623752861078637274073974934980 : ((((p1 ∨ ((p4 ∧ ((((p5 → True) ∧ (p4 → ((False ∧ True) ∨ True))) → p5) ∧ (p4 → True))) ∧ (p3 → ((False → p4) → p1)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_241302628566135669122166088967 : ((False → True) ∧ (((False ∧ p3) → (p5 ∨ p1)) → (((p3 ∧ True) ∨ (p4 ∨ (p5 → ((((p4 ∧ (p1 → p5)) ∨ p1) ∧ p3) ∨ True)))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88011421142905265895283032952 : (((((True → p5) → p4) ∧ p5) ∧ ((p3 ∧ ((False ∧ True) ∧ p5)) → (((p1 ∧ p4) ∧ ((((p3 ∨ p3) ∨ p4) ∨ p1) ∧ p1)) ∨ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (True → p5) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556913257376862039421345788630 : (((p3 ∨ ((((((False ∧ False) → True) ∧ False) ∨ ((True ∨ True) ∨ (p3 ∨ p4))) → p4) ∨ (((p1 ∨ p3) ∧ False) ∨ (True ∧ (p5 → True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314267830170807457403374645640 : (p3 ∨ (((False → p2) → (((p4 ∧ p1) → (p3 ∨ p5)) ∨ ((True ∧ (p4 ∨ p5)) → (((p2 → p5) ∨ p4) ∨ p2)))) ∨ ((p3 → True) ∧ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156609276323538470093887405209 : (((((p5 → p3) → (((p3 → p5) ∧ (p5 ∧ (True ∨ ((p1 ∧ p3) ∧ p1)))) → p2)) ∧ True) ∧ p5) ∨ ((((p5 ∧ p3) ∨ True) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95516247083379035330143862231 : ((p5 ∧ ((((p5 ∨ p2) → (p4 ∨ False)) ∧ ((p1 ∨ ((p2 → p1) ∧ (p2 ∧ (p2 ∧ True)))) ∧ (p5 ∧ (p5 ∨ p1)))) ∧ (False ∨ p2))) → p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : (p5 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h23 : (p5 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h24 := h6 h23
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h9.left
    let h35 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h37 =>
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h39 : (p5 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h40 := h6 h39
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- False on the left can always be used.
          apply False.elim h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h44 =>
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h46 : (p5 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h47 := h6 h46
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- One of the premise coincides with the conclusion.
          exact h48
        case inr h49 =>
          -- False on the left can always be used.
          apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180139889966313574473890001554 : ((((p4 ∧ (((p4 → (True ∧ (p2 ∧ p2))) ∧ p4) → p5)) → p5) → p1) → ((p5 ∧ (p2 ∧ ((p2 → p5) ∧ p5))) → (p1 ∨ (p5 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706842913709592286456033555848 : (((((p1 ∨ ((p1 ∨ True) ∨ (True ∧ True))) ∧ p3) ∨ ((((p4 ∨ p4) ∨ True) → ((p5 ∧ p2) ∨ (p5 → p5))) ∨ ((p5 ∨ True) → False))) ∨ p5) ∧ True) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158298096968927434087266307890 : ((((p2 ∧ p3) → True) → (((p5 ∧ (p3 ∧ (p3 ∧ (False ∨ False)))) ∧ p2) ∧ ((True ∧ p5) ∨ p2))) ∨ ((p3 → p1) ∨ (False → (p2 → True)))) := by
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
theorem thm_5_vars_147709693409822658466493037708 : ((((p4 ∨ (((p3 ∨ True) → (p1 ∨ False)) ∨ (p5 ∨ p5))) ∨ (p4 ∧ (p4 ∧ (False ∨ (p3 → p2))))) → False) ∨ (p3 → ((p3 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50299755129164847456984883913 : ((((p5 → ((p2 ∧ (p2 ∧ (((p4 ∧ (False → True)) ∨ p3) ∨ p2))) → p3)) ∨ (p4 ∨ (False → p4))) ∨ (p1 → ((p2 → False) ∨ False))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227052813611307406949531009711 : (((p2 ∨ p5) → False) ∨ (p5 → (True ∧ (((((p3 ∨ (p1 → p1)) → (((((p3 ∧ p3) → p2) → p2) → p2) ∨ p5)) ∨ True) ∧ p4) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67782175886731033121084468750 : ((p2 → ((True → ((((False → p2) → p3) ∨ False) → (((True → (p2 → ((p4 ∨ True) ∧ p4))) ∧ ((p3 ∨ True) ∧ p3)) ∨ p1))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57749582591921401161221345328 : ((((False → p4) → p2) → ((True ∧ (p2 → ((((False → (p3 ∨ ((p1 ∧ True) ∨ p2))) ∨ p4) → True) ∨ p2))) → ((p5 ∧ p3) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110988428623967531909697105631 : ((((p5 ∧ ((p1 → (p3 ∧ p5)) ∧ ((((p4 → p1) ∧ (p3 ∨ p5)) ∧ (p2 ∧ p3)) ∨ (p4 ∨ True)))) → (p1 → p4)) ∧ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341076760895706283163555795574 : (p2 → ((True → ((((False ∨ False) ∨ ((((p1 ∨ p1) → False) ∧ p3) ∧ p3)) ∨ (p1 → p4)) ∧ ((p1 ∨ ((True → p5) → p4)) ∧ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38540538758957129057936988733 : ((((((p1 ∧ ((False ∨ False) → p5)) ∧ p4) ∧ (p1 ∨ p3)) ∧ ((p3 ∧ p4) → (((p4 → ((p4 ∧ p3) ∨ False)) → p1) ∧ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320457400559553031689385053589 : (p4 ∨ ((True → False) → ((((p3 → ((False → p5) → True)) ∨ p1) ∧ (p1 ∨ (((p3 ∧ p5) ∧ ((p2 → p4) → p3)) ∧ (False ∧ p1)))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718856223689978062529666108143 : (((((p1 → p4) ∨ (p5 → False)) ∨ ((False ∧ (p4 → ((False ∧ False) ∨ p1))) ∨ (p3 ∨ ((False → p2) ∨ ((False → (p5 → p2)) → p3))))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679730444781851201963517213333 : ((((((((True ∧ p3) ∨ (False ∨ p5)) ∧ (p1 ∨ ((p5 ∧ (p4 ∨ p3)) → p4))) → (p4 ∧ False)) ∨ p3) → ((True → p4) → (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43250961672508289395979117436 : ((((False → (((((p1 ∧ ((((p2 ∧ (p2 → p2)) → p4) → p2) ∧ p3)) ∨ ((False ∨ True) ∧ p5)) → p5) ∨ p4) ∧ p1)) ∧ p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_898483492489854512475057208616 : (((((((p4 ∧ ((((True ∨ (False → p3)) → p5) → (False ∨ ((True ∨ p1) ∧ p2))) ∧ p4)) ∨ True) ∨ False) ∨ True) → (True → (p4 ∧ p5))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ ((((True ∨ (False → p3)) → p5) → (False ∨ ((True ∨ p1) ∧ p2))) ∧ p4)) ∨ True) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677339157820549924929154527308 : (((((p5 ∨ ((((True ∨ ((True ∧ (p1 ∧ False)) ∧ False)) ∧ p5) ∧ (p3 ∨ (False ∧ True))) → p5)) ∧ p1) ∨ (p1 ∨ (p5 ∨ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145874875920652518623691852396 : (((p2 ∨ p5) → (((p1 → (p2 → p5)) → ((p1 → (p4 → p1)) → p1)) ∨ (p1 ∨ (True ∨ (p2 → p5))))) ∧ (((True → p5) ∧ True) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792226424100008378565082941642 : (((True → ((True ∧ (False ∧ (p1 ∧ (p1 ∨ ((False → False) ∧ (((p4 ∨ p4) ∨ True) → (p5 ∨ p2))))))) ∨ (((p2 ∧ True) ∧ p5) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800003717702348064901491407093 : (((p2 → ((((((p3 ∨ p4) ∧ ((p3 ∧ ((p1 ∨ p2) → (p2 → True))) → (p3 ∨ (False → True)))) ∨ p4) ∨ True) → (p5 ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157765889173261030141622659699 : (((p3 ∨ (((p3 → (p5 → p3)) ∧ (p2 ∨ (p4 → p1))) → p4)) ∧ (p5 ∧ (p2 → (False ∧ p3)))) ∨ (((p3 → (False ∨ p3)) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657017388561120655642660528274 : ((((((p4 ∨ p4) ∧ p3) ∧ ((p1 → ((p4 ∨ (p2 → (p2 → (((False → p2) → p1) ∨ p2)))) → True)) → (False ∧ p3))) ∨ (p5 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62339308978594538413793398121 : ((p3 ∧ ((((p2 ∨ ((False → False) ∨ p4)) ∧ ((p1 ∨ False) → ((p1 ∧ (p4 → (p2 → p1))) ∨ True))) → p4) ∨ (True ∨ (p4 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698149718266103842927516218282 : ((((((((p4 → True) ∨ True) ∧ (p3 ∨ (p2 ∨ True))) ∨ p5) → False) ∨ (p3 → (p5 → (p5 ∧ (True ∨ (((p2 ∨ p2) → p4) ∧ False)))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64788930964326422025353597020 : ((p2 ∨ (((p2 ∧ (p3 ∧ (((False ∨ p1) → (False ∨ (p4 ∨ True))) → p4))) ∧ ((p5 → (True ∧ p2)) → ((p3 ∨ p4) ∧ p4))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166716591025120694517818450879 : ((p3 → ((True ∨ (False ∧ p1)) ∧ ((False ∨ (p5 ∨ ((p1 ∨ p2) ∧ p2))) ∨ (True ∨ p1)))) ∨ (True ∧ ((((p5 ∧ p5) ∨ p2) ∧ False) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_985436745629104149462603817134 : (((p2 ∧ ((((p2 → (p2 → p4)) → (((p3 → ((p4 → p4) ∨ (p5 ∨ (False ∨ False)))) ∧ p5) ∧ p3)) ∨ ((True ∨ p5) ∨ p2)) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → (p2 → p4)) → (((p3 → ((p4 → p4) ∨ (p5 ∨ (False ∨ False)))) ∧ p5) ∧ p3)) ∨ ((True ∨ p5) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112494701564465319613364060525 : ((((p4 ∨ ((True → False) ∨ (((False ∨ (p3 ∨ (p4 ∧ (p2 ∧ p3)))) ∨ ((p1 ∧ p2) → (p4 ∨ p4))) ∨ p1))) ∨ p1) → p1) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330864159289533372789512103599 : (True → (p3 → ((p2 ∨ ((p5 ∧ (p1 ∧ True)) ∧ (p5 → (True → (p2 → (p5 ∨ False)))))) → (((p2 → p3) → p2) ∨ (p1 ∧ (False → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51258958000407412666895591966 : ((((p1 ∨ p4) ∨ ((True → p5) → (((p2 ∨ p4) ∨ (p5 ∧ (True ∧ p2))) ∧ (p5 ∨ False)))) ∨ (False → (p2 ∨ ((p2 → p3) ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345673869058682511162656683644 : (p3 → ((p1 ∨ (False ∨ ((((((p2 ∧ p4) ∧ p3) → False) → (False ∧ p4)) ∧ (p3 ∨ ((p1 ∧ ((False ∨ p4) ∨ p5)) → True))) ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137658375935546503147717330668 : ((False ∨ (False ∧ ((p5 ∧ (p2 → (((False → (((p2 ∨ False) → (p2 → p1)) → p3)) ∧ (p1 → p5)) ∧ p5))) ∨ p1))) ∨ ((p3 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186949980903402230874316901394 : ((((p2 → p3) ∧ p5) ∨ ((True ∨ p1) ∧ ((p5 ∨ p3) ∨ p3))) → (((p4 → p5) ∨ ((p5 ∨ p5) ∨ (p1 ∨ True))) ∨ ((True ∧ p2) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
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
      case inr h12 =>
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
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187567285615645916763747619127 : ((p3 ∨ (((((True ∨ (False ∧ p1)) ∨ p1) ∨ p5) → True) ∨ True)) → ((((p1 → ((p1 → False) → p5)) → p1) → (p3 ∧ False)) ∨ (False → p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51909429044443394643225081180 : (((((((p5 ∧ (False ∧ p5)) ∨ p2) ∨ ((p2 ∨ p1) → p5)) ∨ p3) ∨ (p3 ∧ True)) ∨ (False ∨ (((p4 → True) ∧ p1) ∧ (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324719302558693791944804771573 : (p5 ∨ (((p3 → p2) ∨ p1) → ((((p2 → (p2 ∨ p4)) ∧ p4) ∨ p4) ∨ (p4 ∨ (p5 → (p2 ∨ (((False → (False ∨ p5)) → p5) ∨ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133750530197332134255983262500 : (((((p3 → (((False → False) ∨ True) → p3)) ∨ True) → ((p1 → ((p4 ∨ p1) ∨ False)) → ((True ∨ p5) ∧ False))) ∧ p2) ∨ (p3 → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321033736375159359127727812337 : (p4 ∨ (False ∨ (p2 ∨ (((((False → p5) ∧ (True → False)) → (((((True ∨ p5) ∧ p3) ∧ True) → False) ∧ (p2 ∨ (True ∧ p2)))) ∨ p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h20 := h18 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178501824319671293560555553290 : (((p3 ∨ ((False ∨ ((p1 → p5) ∧ p3)) ∧ p2)) ∨ (p1 ∨ (p2 → True))) ∨ (p3 ∨ (p1 → ((p3 → ((p4 ∧ True) ∨ p3)) ∨ (p1 → p4))))) := by
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
theorem thm_5_vars_257174803411795269074170259289 : ((p2 ∨ p1) → (p2 → ((False ∨ ((p2 ∧ True) → (p5 → (p4 → (p3 ∧ (False ∧ False)))))) ∨ ((p4 ∧ (p3 ∨ ((True ∧ p5) ∨ p4))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346350598870585100244869823913 : (p3 → ((((p4 ∧ p1) ∨ p5) ∧ ((p5 ∧ ((((True → ((p1 ∨ p1) ∨ p2)) ∨ p5) → ((p5 → p3) ∧ p1)) → p5)) → p4)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677576642738905843885502604648 : (((((p4 → (True ∧ (((p4 → (((False → p3) ∧ (p4 ∨ p2)) ∨ p2)) → (p5 ∨ False)) ∨ True))) ∨ p4) ∨ ((p3 → False) → (p3 ∧ False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664813058390234774205164811867 : ((((p1 → (False ∨ (p3 ∧ ((p4 ∧ (((((p3 ∧ ((p5 ∧ p3) ∨ True)) ∧ p1) ∨ p1) → p1) → p4)) → (False ∨ False))))) → (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152448354864898162155568703526 : (((True ∧ (p4 ∨ p3)) ∧ ((((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) → False)) → (False ∧ (p3 ∧ (p5 ∧ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h17 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h25 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h26 := h21 h25
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h28 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h29 := h21 h28
    -- False on the left can always be used.
    apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h34 =>
    -- One of the premise coincides with the conclusion.
    exact h34
  case inr h35 =>
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h36 : (((True → ((p3 ∧ False) ∧ (p1 → (p2 → (False ∨ p2))))) ∨ True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h37 := h31 h36
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324827230417166191040250212905 : (p5 ∨ ((p3 ∨ True) ∧ (False ∨ ((p1 ∨ (False ∨ ((p1 ∨ ((False ∧ True) → ((p3 ∨ (p2 ∧ p3)) ∨ p1))) ∨ ((False ∨ p1) ∧ False)))) ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113665973109872961417432231529 : (((((True ∧ ((((True ∧ p2) ∨ p1) ∨ ((False ∧ (p4 → p1)) ∧ ((p2 ∨ p3) ∨ False))) ∨ True)) → p3) ∨ False) → (p1 → False)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60014703018178860726225584455 : (((p1 ∨ False) → ((True ∧ (p4 → (p4 ∨ (p2 ∨ ((True ∧ (False → (p1 ∧ False))) → ((p4 ∨ ((p2 → p5) ∨ p5)) ∨ p5)))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228229962555399975538273979178 : ((p5 ∧ (p4 ∨ p3)) ∨ ((((p5 → p2) ∧ (p2 ∧ True)) → ((p1 ∧ (p3 → ((p4 ∨ p2) ∨ (p4 ∨ False)))) ∨ False)) ∨ (True ∧ (p3 ∨ True)))) := by
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
theorem thm_5_vars_172363845913121178712660868616 : ((((p5 ∧ p2) ∧ ((p4 ∧ p4) → p3)) ∨ (p3 → (p1 ∧ (p5 ∨ (True ∧ p2))))) ∨ (False → (((p1 → True) → (False ∨ (p1 ∨ True))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61356240476689360228360926319 : ((p1 ∧ (((p1 → p1) ∧ (False ∧ ((((p1 ∨ (p3 ∧ (p1 ∧ p2))) ∨ p4) → ((p2 → p5) ∨ (p3 ∨ (p4 ∨ p2)))) ∧ p3))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205670110128088732147220684739 : (((p2 ∨ p1) ∨ ((p1 ∨ p2) ∧ True)) ∨ (((((p2 → p1) ∨ p2) ∧ p5) ∨ ((p1 ∧ (p3 → p1)) ∨ p5)) ∨ ((p3 → p4) ∨ (False → p1)))) := by
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
theorem thm_5_vars_56072627915436637270127425609 : ((((p4 ∧ (p5 → p1)) → False) ∨ (True ∧ (((((True ∧ p3) ∧ False) → ((p5 → (p5 ∨ (p4 ∧ True))) → False)) → (p2 ∧ p2)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117711623525304767311361314832 : ((p3 ∧ (p5 ∧ (p2 → (((((p5 → (p5 → (p5 ∨ (p1 ∧ (True ∧ p1))))) ∧ True) ∧ p2) ∨ False) → ((p1 → p4) → p4))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218177460635533761410182966235 : (((False ∧ p3) ∨ (False ∨ p4)) → ((True → ((((p4 → p2) → (True ∧ p3)) → (False → False)) → (p1 ∨ ((p5 → False) ∧ p1)))) ∨ (p2 → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157646945683987918096502211795 : (((p4 → (((p3 ∨ (((p5 ∧ True) ∨ p3) → (False ∧ False))) ∨ p5) ∨ True)) ∧ ((True ∧ p4) ∧ True)) ∨ ((True → p1) → ((False ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205332772779369921262583771008 : (((p2 → (p5 ∧ True)) ∨ (False ∨ p4)) ∨ ((((p5 → p1) → p4) ∨ (p2 → True)) → (((p5 ∧ (((p5 → p5) ∨ True) → p3)) ∧ p2) → p5))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164544823802809147205193003206 : (((((p1 → (p1 ∧ p3)) → ((p1 ∨ True) → p5)) ∨ (p4 ∧ ((True → p1) ∨ p5))) ∧ p2) ∨ ((p5 → p3) → (((p2 ∨ p3) ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239173093097177589352625535746 : ((p2 ∨ True) ∧ (((((True → p1) → False) ∨ (p4 ∧ p5)) ∨ True) ∨ (((((p2 → p2) ∨ p3) ∧ True) → ((p4 → (p3 ∨ False)) ∨ p5)) → False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38035468189758462607842353528 : ((((((p5 → (p1 ∧ (p3 ∨ (p5 ∧ ((True ∨ p2) → ((p5 ∨ ((False ∧ p2) → p5)) ∧ p3)))))) ∨ p3) ∨ p1) → (p4 ∨ p1)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341059820565935593626507750635 : (p2 → ((p3 ∨ (((((p4 → (True ∧ ((p2 ∨ p5) ∧ (p1 → p4)))) ∨ p4) ∨ (p3 → p2)) ∨ False) → ((p4 ∧ p1) → (False ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219497125820155916878886444067 : ((p5 ∨ ((True ∨ p4) ∨ False)) → (((p5 ∧ ((True ∧ (((p2 ∨ (True → (False → p5))) → (p5 → False)) ∧ p2)) → p5)) ∨ True) ∧ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
      -- False on the left can always be used.
      apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751968204264345320656032077400 : (((True ∧ (p4 ∨ ((p2 ∧ ((False ∧ p5) → False)) → (p3 ∨ ((p1 → ((p2 → (p5 ∨ (p3 ∧ (p3 → True)))) → (p4 ∧ p1))) ∨ True))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_194234914578598631385959163555 : ((p4 → ((False ∧ (p4 ∧ (True → (p3 → p4)))) → p2)) → (True ∧ (((True ∧ (True ∨ (p5 ∨ (p4 ∨ p5)))) → (p2 → p4)) → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52616186074471930084644685985 : (((((p3 ∧ p3) → p1) ∧ ((p3 ∧ (False ∨ p3)) ∧ ((p4 → True) ∧ p2))) ∨ (((((p1 ∧ True) ∧ True) → p4) → (p4 ∨ p3)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328518109794806364943229862258 : (True → ((((p2 ∧ p3) ∨ ((False ∧ True) ∧ (p2 ∨ (False ∨ (p3 ∨ p5))))) ∨ (True → True)) ∨ ((((p3 ∨ p4) → (p3 → False)) ∨ p5) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256273194093841113734282477873 : ((False ∨ p1) → ((((p1 → p2) ∨ ((((False ∧ p2) ∨ p1) → p2) → ((((p4 ∧ (p4 → (True → p3))) ∧ p2) → False) ∧ p3))) ∨ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40498707657523615526061066130 : ((((True ∧ (p1 ∨ ((True ∨ True) → (((p4 → True) ∧ (p5 ∨ p2)) ∧ (((((p1 ∧ p2) ∨ p5) ∧ p2) → p2) ∧ p2))))) ∨ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259432400728640113911514145019 : ((False → p4) → ((((False ∧ (((True → p1) ∧ p2) ∨ False)) ∧ (((p4 → (True ∨ (False ∨ p4))) → True) ∧ True)) ∨ ((p2 ∧ p3) → True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342652808335483895678766394041 : (p2 → (((((True → (p5 ∨ (True ∨ p3))) ∨ p4) → p4) ∨ p3) ∨ ((p1 ∨ (((True ∧ p2) ∨ True) ∨ (p5 ∧ p5))) → ((p1 ∨ p2) ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65745075742495645566869525619 : ((p4 ∨ ((((p5 ∧ (p1 ∧ (p4 ∨ ((p5 → (p3 → p4)) ∧ ((False ∨ p3) ∨ p3))))) ∧ (p3 ∨ p3)) ∧ p3) → (True → (p1 ∧ p4)))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h9
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h30.left
  let h32 := h30.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h35 =>
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h42 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h43 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h44 := h37 h43
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h45 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h46 := h44 h45
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h47 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h48 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h49 := h37 h48
          -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
          have h50 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h49, we can now drive its conclusion.
          let h51 := h49 h50
          -- One of the premise coincides with the conclusion.
          exact h51
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h53 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h54 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h55 := h37 h54
        -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
        have h56 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h55, we can now drive its conclusion.
        let h57 := h55 h56
        -- One of the premise coincides with the conclusion.
        exact h57
      case inr h58 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h59 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h60 := h37 h59
        -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
        have h61 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h60, we can now drive its conclusion.
        let h62 := h60 h61
        -- One of the premise coincides with the conclusion.
        exact h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218126797008525940692436889475 : (((p3 → True) ∧ (p4 ∧ True)) → (((((p1 ∧ p1) ∨ False) ∨ p3) ∨ (True ∧ ((True ∧ p2) ∧ ((p1 ∨ False) ∨ (p2 ∧ (p2 ∧ p2)))))) ∨ p4)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61719942550254239036949753170 : ((p1 ∧ (True → ((p5 ∨ True) → ((p3 ∨ ((((p1 ∨ False) → p5) → ((True → p1) ∨ (False ∧ (False ∨ (p4 ∧ p5))))) ∨ True)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687606322811068304323373746864 : (((((((p3 ∨ True) → (p1 ∨ (p4 ∧ p1))) → ((p5 ∧ (p5 ∨ p4)) ∧ True)) → p5) ∧ (p2 → ((p3 ∨ p3) → (p2 ∧ (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



