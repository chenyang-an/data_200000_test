variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41933435329758530897141680696 : ((((False → (p4 ∧ p3)) → ((False ∨ p3) ∧ ((p1 → (False → p5)) ∨ (p5 ∧ ((p2 ∨ ((p4 ∨ p3) → (p2 → False))) ∨ p5))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136372799707910538162364645360 : (((((True ∧ False) → True) → p2) ∨ (p5 ∧ (((False ∧ (p1 → (p1 ∨ (True ∧ (False ∧ (p1 ∨ p3)))))) ∨ p5) ∨ False))) ∨ (True ∨ (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49524929280081824010432773951 : ((((((p5 ∧ (False ∨ ((False → ((p5 ∧ p1) → p4)) ∧ p4))) ∧ (p3 → (True ∧ p5))) → p3) ∨ (p3 ∨ p3)) → ((p5 ∨ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111791988467727888303906662895 : ((((p1 ∧ ((True → (((p1 ∧ p4) ∧ (p4 → (False ∨ p1))) → (False → p5))) → (False ∧ (False ∨ False)))) ∨ (p3 → p3)) ∨ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47718279710222983713292347053 : ((((((((p2 → p5) ∧ ((p3 ∧ (p4 → p4)) ∧ ((p5 ∨ (False → True)) ∨ p1))) ∧ (False ∧ False)) ∧ p4) → p5) ∨ p3) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174550225638334708310880386247 : (((((p5 → p1) ∨ p5) ∧ p1) ∧ (((True ∨ p1) → False) ∧ ((True ∧ p2) → p5))) → (((p1 → (True ∨ (p2 ∨ p3))) → (False → p5)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161816555433961599950099175727 : ((p5 ∨ (p5 ∧ ((True ∧ ((((True ∨ (p3 ∨ True)) → p2) ∨ False) → ((p4 ∨ False) ∧ p5))) ∨ p4))) → ((True ∧ ((p3 → False) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317730713811488650503742324481 : (p4 ∨ ((((((((p4 → False) ∨ p1) ∨ True) → ((False ∨ ((False ∧ p4) → False)) ∨ (True → p4))) ∧ p2) ∧ p4) ∨ (p4 → (p5 → True))) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237964564594603962777406314479 : ((True ∨ False) ∧ ((p5 → (p1 → p3)) ∨ (((p3 → p4) ∧ ((((p3 ∧ p4) → p1) ∧ ((p1 ∧ False) ∨ ((p1 ∨ True) → p5))) ∧ p3)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177797857800222680481851405800 : (((p2 ∨ ((p4 → (False ∧ (False ∧ p1))) → ((p2 ∧ p3) ∨ p2))) ∧ True) ∨ ((p4 ∨ False) ∨ (p1 ∨ (True ∨ ((p3 ∧ p3) ∧ (p5 → False)))))) := by
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
theorem thm_5_vars_48849744163475659453735731038 : (((p2 ∨ ((p3 → (((p3 ∨ p4) → ((False ∨ False) ∧ (p3 ∨ (p5 ∨ p5)))) ∨ p5)) ∧ ((False → p5) → p5))) ∧ (p1 → (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700099278552706632278113883742 : ((((((p5 ∧ p5) → p3) → (p5 ∧ ((p4 ∧ (p3 ∧ p2)) ∨ p3))) → (((p1 ∨ (p2 ∨ ((True ∧ (p3 → p5)) ∨ False))) → p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106778769838530186928284196018 : ((((True ∧ (p5 → (True ∧ True))) ∧ p4) → (((True → (p4 ∧ ((p4 ∨ p2) ∨ p3))) → p1) ∨ (((p3 → p5) → p3) ∨ p4))) ∧ (p1 → p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114127770833955794068272300220 : (((p3 → (p1 ∨ (((True → ((p3 → p1) ∧ True)) ∧ ((p4 ∧ p1) ∧ (p1 ∧ (p4 → p1)))) ∨ p5))) ∨ (p3 → (p1 ∨ p3))) ∨ (True → p3)) := by
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
theorem thm_5_vars_256421970159756590219858000561 : ((False ∨ p3) → (((p2 ∨ p1) ∨ (p1 ∧ (False → p5))) ∨ ((p1 ∨ ((p3 ∨ (p4 ∧ (p3 → (p2 ∨ p5)))) → p1)) ∨ ((p4 ∨ p3) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183856393887948963710360252050 : ((((p1 → ((p4 → p1) ∧ (False ∨ p2))) → (p2 ∧ p3)) ∧ p1) ∨ ((p1 ∧ (((False → p2) → (((p1 → p4) ∨ p1) → p1)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65651911777215120700255376457 : ((p4 ∨ ((p4 ∧ ((p1 → ((p3 ∨ p5) ∧ True)) ∨ ((False → p2) ∧ ((True ∨ (((False ∧ p5) ∧ (p1 → p2)) ∧ p2)) ∧ p3)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44659141183099093798630233345 : ((((p4 ∧ (True → (p2 ∧ (p1 ∧ p3)))) ∨ ((False ∧ (p4 ∧ True)) ∨ (True ∨ (((p2 ∧ (p4 ∨ p3)) ∨ (p4 ∧ p3)) ∧ True)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42727854659794566861410321315 : (((True → ((((p1 ∧ p4) ∧ True) → (((False ∧ p3) ∧ (True ∧ (p5 → ((False → p3) → (p2 ∨ False))))) ∨ (True → p3))) ∨ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678037098248501499098255907228 : ((((((p1 ∨ ((False ∧ (((p2 → True) → p1) ∨ True)) ∧ False)) ∧ (p3 ∨ True)) ∨ (p3 ∨ (p2 ∨ p3))) ∨ (((p5 → p1) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244191080217951435905346631740 : ((True ∧ p5) ∨ (((p2 ∨ p5) → ((False ∨ (p4 ∨ (p4 ∧ (True ∨ False)))) ∧ ((False ∧ p5) → (((False ∨ p2) ∨ p3) ∨ (False → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262163364357032196631741488803 : (True ∧ ((((p5 → False) ∨ (p3 ∨ ((p1 → ((p2 ∨ ((True ∧ p5) ∧ p1)) ∨ ((p2 ∧ ((False → p2) → p2)) ∧ p1))) ∧ p5))) ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50353783585534222835865917839 : (((((p5 → p4) → (p3 ∧ False)) ∨ ((p1 ∧ p3) → ((((p1 → (p1 ∧ p3)) ∨ False) → p1) ∧ False))) ∨ ((False ∨ True) ∨ (False → p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170356259880451009128271631165 : (((p4 → (p5 → (True ∧ True))) → (((p4 ∨ True) ∨ (True ∨ p3)) ∨ (p4 → p4))) ∧ ((((True → False) ∨ (p3 → True)) → (p5 → p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199713980222222815842922773113 : (((p4 ∧ (((p3 ∧ p2) ∧ True) ∨ p5)) → False) → (((True → (p2 ∧ (p1 ∧ p3))) ∨ (p2 ∨ (p4 ∧ (p1 ∨ p2)))) ∨ ((p5 ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336128641617235314871353555232 : (p1 → ((((p2 ∧ (p2 ∧ p3)) ∧ (p5 ∨ ((p5 ∨ p5) ∧ (p5 → ((p5 ∧ (True ∧ (False → ((p5 ∨ p1) → p5)))) ∧ p1))))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110869623208517406193421409701 : ((((((False → p5) ∨ (False ∧ (((False → p3) ∧ p5) ∧ ((True ∨ (((False → p3) ∧ p3) ∧ p2)) → p2)))) → p3) → p1) ∧ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775185301182900526328175392872 : (((False ∨ ((p1 → p3) ∨ ((((p5 → (p4 ∧ ((p5 ∨ p4) → True))) ∧ True) ∧ ((((p5 ∨ p3) ∧ False) ∧ (p3 ∧ p2)) → True)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344329829805808860046359678956 : (p2 → (p3 ∨ (False ∨ (((p5 ∨ (p1 ∧ ((p2 ∧ p2) ∨ ((p5 → p4) → p2)))) ∨ (p4 ∧ True)) ∨ ((p2 → (False ∧ (p3 ∧ False))) → p1))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300664061389986400236592308476 : (False ∨ (((True ∧ (((False ∨ (((p3 → (p5 ∧ p4)) → p2) → (p5 ∨ p5))) → p4) ∨ p5)) ∧ p4) ∨ (((True → p4) ∨ True) ∨ (False ∧ True)))) := by
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
theorem thm_5_vars_164777273541609705059113596363 : (((((((p4 → p4) ∨ True) → p1) ∨ p5) ∧ (((p3 ∨ p2) → (True ∧ p5)) ∧ p2)) ∨ p2) ∨ (False ∨ ((((p1 ∧ p3) ∧ p4) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658126261961980207033715504749 : ((((p4 ∧ ((True ∧ (((p3 → p4) → ((False ∧ ((False ∨ ((p1 ∧ p5) ∨ p3)) ∧ p3)) ∨ p1)) ∧ (p5 ∧ False))) ∨ p4)) ∨ (False → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316878664373296481992227087127 : (p3 ∨ (p1 → (((((True ∧ p1) → p1) ∨ True) ∨ p3) → (p1 ∧ ((p1 ∧ (True → (((False ∧ (False → p5)) ∨ p3) ∧ True))) → (p3 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h21 := h9 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_554066823991976345790040198996 : (((p2 ∨ (((p2 ∨ (((p4 ∧ p4) → True) ∨ (False ∧ p3))) → False) ∨ ((((p4 → (p2 ∧ (True ∧ (p5 ∧ False)))) ∧ True) ∨ True) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179249089360433969866871342139 : ((p5 ∧ (((p5 ∨ p3) ∧ False) ∧ (((p3 → (p3 ∧ True)) → True) ∧ p5))) ∨ (((p4 ∨ p1) ∨ (p4 ∨ (p4 ∨ (True ∨ (False ∨ p5))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147364151329694501355145385550 : ((((p3 → (p1 → (p2 → ((p1 ∨ p2) → ((p1 ∨ (False ∨ True)) ∨ p1))))) → (p4 ∨ (p2 ∨ p1))) ∨ p4) ∨ ((p5 → True) ∧ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116553871192793296515825740567 : (((p1 ∨ p2) ∧ (((p1 ∨ p2) ∨ p4) → ((p2 ∧ (False ∧ ((p3 → ((p1 ∨ p3) → p4)) → (p3 → (True ∧ p2))))) ∧ p5))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191447285719757447485161086930 : (((False → p4) → ((p1 → ((p5 → p4) ∨ p2)) ∧ p4)) ∨ ((((False ∨ p1) ∨ (True ∨ (False ∨ ((p5 ∧ p5) → p3)))) ∨ p1) ∨ (p4 ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177739873069050498441950145561 : ((((p1 ∧ (True ∨ True)) ∨ (((p5 ∧ p5) → p1) ∧ (p5 ∧ False))) ∧ p4) ∨ (True → (True ∨ (p4 ∧ (((p2 ∨ p2) ∨ p1) → (p4 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56316002564679139178266882541 : ((((p1 ∨ (True ∨ p5)) ∧ p3) → (((p4 ∨ p2) → (p4 ∨ (p4 ∨ (p5 ∨ True)))) ∧ (p5 → (p5 ∨ ((p1 → p4) → (p5 ∨ p1)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55531471047578519557727160837 : ((((p3 ∨ p4) → (p2 ∧ (p3 → p4))) → ((((p2 → p1) → p2) → (p4 ∧ ((((p4 → p2) ∨ (p1 ∧ p4)) ∨ False) → p1))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808554042491581676746622118386 : (((p4 → (p5 ∨ (p3 ∧ (((((((p3 → p1) ∨ (p1 → True)) ∨ ((False → p5) ∨ p2)) ∧ True) ∨ (p1 ∨ (True ∨ p3))) ∧ p1) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357982935887360276698083730098 : (p5 → (False ∨ ((p5 → ((p2 → (((True → ((((p1 ∨ p2) ∧ (p3 ∨ p3)) ∧ p4) ∨ ((p2 → p2) ∨ p4))) ∨ p5) ∨ False)) ∧ False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344126532471383223681800707877 : (p2 → (False ∨ (((p1 ∧ (p1 ∧ (True ∧ (p3 ∨ (False ∧ (p1 → True)))))) ∧ p5) ∨ (p2 ∨ (p1 ∨ ((p4 ∧ p3) → ((True ∨ p4) ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83260480504554305921175935187 : (((((False ∨ (p2 ∨ ((p1 ∨ (True ∨ p5)) → (False ∧ (p5 → p3))))) ∧ p1) ∧ (p1 → p4)) ∧ (p2 → (p5 ∧ (p4 → (p2 → False))))) → p4) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626206182581937745626023662687 : ((((p3 → (((((p3 ∧ p2) ∨ p5) → ((p4 ∧ (p3 ∨ p2)) ∨ (p1 ∧ (p4 → p1)))) ∨ ((False → p4) → False)) ∨ (p2 → p3))) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205858249559646648273852325256 : (((p4 → p2) → ((p4 → p1) → False)) ∨ ((((True ∧ p5) ∨ False) ∧ (False ∧ ((p4 → ((p4 ∨ ((p2 → p5) → False)) ∨ p1)) → p5))) → p4)) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300558386352457655364435930519 : (False ∨ (((p3 ∧ (p3 ∨ False)) ∧ ((((((p1 ∨ (p4 ∧ p2)) ∨ (True → p2)) → p4) ∧ p4) ∧ p1) → p3)) ∨ (True ∨ (p4 ∧ (p2 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208485236983463664734653017024 : (((True ∧ False) → ((p3 ∨ p2) → False)) → (((((True ∨ True) ∧ (((p3 ∧ p2) → (p5 ∨ True)) ∧ (p4 → p3))) → False) ∨ (True ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184447177073480805091074700600 : (((p3 ∧ (((False ∧ p5) ∨ True) ∨ (p2 ∧ p4))) ∧ (p3 ∧ p1)) ∨ (((p2 → p1) ∨ False) ∨ (p2 ∨ (False → (((p2 ∧ p2) → p5) → p2))))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41654962199908470091957703280 : (((((p1 ∨ p2) → (False → (p5 ∨ p1))) ∧ (((False ∨ False) ∨ (True → (p2 → (p4 ∨ p5)))) → ((p2 → (p4 ∧ p1)) ∧ p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337525820756935327890744768461 : (p1 → (((((((True ∨ p1) → (p3 ∧ p3)) ∨ p5) → ((p3 → p3) ∧ False)) → ((p2 ∨ p4) ∧ p3)) → p4) ∨ (False → ((p1 → p1) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310983550568684427989217540734 : (p2 ∨ ((False → p3) ∧ ((p1 ∧ (((p3 ∧ False) ∧ (p4 → False)) ∧ p1)) ∨ (p5 → (((((True ∧ p5) ∧ True) ∧ p2) ∧ p4) → (p2 ∨ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180586250546576972935784197426 : (((p4 ∧ (p2 ∧ ((True → p4) ∨ (p3 ∧ True)))) → ((p5 ∨ p2) ∨ p1)) → (((p4 → (p3 → (True ∧ p4))) → (p4 ∧ p5)) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811485199046510305523948807597 : (((p5 → (p4 ∨ ((p4 → (p3 ∨ p4)) → (False ∨ (p3 ∧ ((p3 → (((False → ((p4 → True) ∨ p5)) → p5) ∨ (True → p1))) ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301263586244267146473406647956 : (False ∨ ((p4 ∧ (((p3 ∨ p1) → p1) → True)) ∨ (((p1 ∧ (False ∨ True)) → ((p3 ∨ p5) ∧ (p2 ∨ ((p5 ∨ (p1 ∧ True)) → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250801920919483211276035692746 : ((p1 → p2) ∨ (((True ∧ ((p1 ∧ (p3 ∧ p2)) → ((((p4 ∧ p1) ∨ False) ∧ ((p4 → False) ∧ (p2 ∧ (p2 ∧ p5)))) ∨ p1))) ∨ p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42558319158837157950143244362 : (((p1 ∨ (p1 ∨ (((p4 ∨ ((p5 ∧ False) ∨ (((p1 ∨ p3) ∧ (((True → p4) ∨ p2) ∨ True)) ∧ p1))) → p3) ∨ (p3 ∨ True)))) ∨ p3) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137667004672358058794442697700 : ((False ∨ (p2 ∨ (p3 ∨ (((False ∨ (p4 ∧ False)) ∨ (p4 ∧ ((True → (p3 → (p1 ∨ False))) ∧ p2))) ∧ (True ∨ False))))) ∨ (p5 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345380415406056611358097678065 : (p3 → (((p1 ∧ ((((p3 → (p2 ∨ False)) ∨ p2) ∧ ((p2 ∨ ((p1 → p4) ∧ ((False ∧ p4) → p5))) → (p4 ∧ True))) ∨ p1)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54258231195495819901511606875 : (((((False ∧ (False ∧ True)) ∧ p2) → (False ∨ p4)) ∧ (p4 ∨ (p1 → ((p5 ∧ ((False ∨ (p1 → (p3 ∨ False))) ∧ False)) ∧ (p1 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244697096488073028803649892279 : ((p1 ∧ True) ∨ (((p3 ∧ p3) ∨ (((p4 ∨ p5) → p4) ∨ ((p4 ∨ p1) ∧ p2))) ∨ ((p4 ∨ (p5 → (p4 → ((p2 → p4) → p5)))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670287264700200409021054513848 : ((((((p2 ∧ True) ∧ p1) ∧ ((((p2 → p1) ∧ False) ∨ ((p4 → (False ∨ (p4 → p3))) → p1)) ∧ (False ∨ False))) ∨ (False ∨ (p2 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49897894042845950648708328671 : ((((p5 ∧ (p3 ∨ (False ∧ (p5 ∨ ((p4 → (True ∨ (p3 ∨ p3))) → ((p4 ∨ p3) ∧ False)))))) ∨ p1) ∧ ((p5 ∧ p5) ∧ (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263157960306155637971893137401 : (True ∧ ((p4 ∧ ((((((p1 → p5) ∨ (((p3 → p3) → p1) → (p5 → True))) ∧ ((True → p1) → True)) ∧ p1) → p2) ∧ p5)) ∨ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177926647341372007224857474155 : (((((p4 ∧ (p4 ∧ p4)) ∨ False) ∧ ((p3 ∨ (p1 ∧ p3)) ∨ p5)) ∨ p2) ∨ ((p1 → p1) → (((p5 ∧ p2) ∨ ((p5 ∧ p1) → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263699470912702530583005840726 : (True ∧ ((((p4 ∧ True) → p2) ∨ (((p2 ∨ p3) ∨ ((p5 → p2) ∧ (True → (True → True)))) → p5)) ∨ (((p1 → p1) ∨ p5) → (p5 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118536189442578826706347051422 : ((p3 ∨ (p4 ∧ ((p3 → p4) ∧ (((((True ∨ (p3 ∧ p2)) → (False → p1)) ∨ (((p4 ∨ p2) → True) → p3)) → p4) ∧ p2)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198815554017565300479304336402 : ((p1 → ((False ∧ ((p4 ∧ p5) → p1)) ∧ p4)) ∨ ((p2 ∨ (((((((p4 ∨ p3) ∨ p1) ∨ False) ∧ p3) ∨ (p2 ∨ True)) ∨ True) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700466823507227029366711869824 : ((((p1 ∨ (False → (((p2 → p3) → (p2 ∨ (p1 ∨ True))) ∧ True))) → (((False ∧ p4) → ((p3 ∧ p3) → p5)) → ((p1 → p4) ∨ True))) ∨ p3) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114949180665954104859251973858 : ((((False ∨ p2) → (((((False → p3) → p1) ∨ p3) ∧ p5) ∨ (p3 → False))) → (((p4 ∧ (p3 → p1)) ∨ (p5 ∧ p1)) ∨ False)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138708807915450768968799230131 : ((((True → ((p5 ∧ False) ∨ (False ∨ (p3 → p1)))) ∨ (((p3 ∧ (p5 ∨ (True ∨ p3))) ∨ (p2 → False)) ∨ p3)) ∧ p3) → (p5 → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
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
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349986429146937194178263782477 : (p4 → ((((((p4 ∨ True) → ((((((p4 ∨ (p5 → p2)) → p5) ∧ True) ∧ p2) ∨ p1) ∧ False)) → (False ∨ p1)) ∨ (p3 → True)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147009185826480076392238730643 : (((((p1 ∧ p3) ∨ ((False ∨ p2) ∧ (p5 ∧ (p3 ∧ ((True ∨ (True ∨ p4)) ∨ p2))))) ∨ (p5 ∧ p5)) ∧ p3) ∨ ((p5 → p5) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688218077576799172439489431622 : (((((False ∨ False) ∧ (((True → ((False ∧ (p3 ∧ p5)) → True)) ∨ p2) → (False → True))) ∧ (True ∧ ((True → p2) → (p3 ∨ (p3 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307444068655681397861497687632 : (p1 ∨ (p5 ∨ (((p4 → (((True → (p1 ∧ p2)) → p1) ∧ (p4 ∨ (True ∧ p5)))) ∨ False) ∧ ((p3 → (p5 → p1)) ∨ ((False ∨ True) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2785692203373682219848553303 : (((p3 ∧ p4) ∨ (p2 ∧ p5)) ∨ (((p5 → False) ∨ (p2 → ((True → ((((False ∧ p3) ∧ p1) ∧ p4) ∧ p2)) → True))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719179065451780068461730473643 : ((((p2 ∧ ((p4 ∧ p4) ∨ False)) ∨ (((((False ∨ ((False → p1) ∧ p4)) ∨ (p2 ∨ True)) ∨ ((p3 ∧ p1) ∨ True)) ∨ p3) → (p2 ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- False on the left can always be used.
          apply False.elim h5
        case inr h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22378459132017783843197666587 : ((((p3 ∧ (p3 ∧ True)) → ((p5 ∨ p5) ∧ True)) → ((((p4 ∨ (True ∨ p4)) ∨ p2) → p1) ∨ (False ∨ ((p3 ∨ True) ∨ (p4 → p1))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200853983635574429559818146315 : ((True ∨ ((True ∨ p2) → ((p1 ∨ p1) ∧ p3))) → (((p5 ∧ (False ∧ ((p2 ∨ (True ∨ p1)) → p5))) ∨ (((True ∨ False) ∨ p2) ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43488956012727699182619998297 : ((((p3 ∧ (p4 ∧ ((p2 ∧ (p2 → p2)) → (((p3 ∨ (((((p3 ∧ p2) ∨ p2) ∧ p3) ∨ p1) ∧ p1)) ∨ True) → False)))) ∨ p3) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318654343401326743830258282043 : (p4 ∨ ((p2 → ((p2 → (p5 ∨ p1)) ∧ (((p2 → (p1 → p5)) ∨ p4) ∧ ((p3 ∨ (((p4 ∧ p1) ∨ p3) ∧ p1)) ∨ p1)))) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147479152861622726062388728453 : (((p2 ∧ (p3 → (((p2 → ((False ∧ p3) → (p5 → p4))) ∨ p4) → (((p5 → p3) → p5) ∧ p4)))) ∨ True) ∨ ((p3 ∧ (p4 → p1)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179559197755329911648473506962 : ((p2 → (((p2 ∧ (((p5 ∨ False) ∧ (p2 → p3)) → p3)) → p1) ∨ p3)) ∨ ((p1 → p1) → ((True → (p4 ∧ False)) ∨ ((p5 → p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257507040561964822374634968711 : ((p3 ∨ False) → (((((p5 → (((p1 ∧ p5) ∨ (True → p5)) → p3)) → p4) ∨ (p3 ∨ p1)) → (p1 → p3)) → ((p3 → (p4 ∨ True)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205374007936164026920330514201 : ((((True ∨ p3) ∨ True) → (p2 ∨ p5)) ∨ (p4 ∨ (((p2 ∧ p2) ∨ ((True ∨ (p2 → ((p5 ∧ (p2 ∧ False)) → p1))) ∨ (p2 ∨ p4))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_613001908837854241923628026 : (((p1 ∧ ((p3 ∨ (False ∧ (((p2 → (p4 → (p4 ∨ p3))) → (False ∧ p3)) ∨ False))) → (p4 ∨ (p1 ∨ p1)))) ∧ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658878582790436943901505177058 : ((((True → (True → (((p3 ∧ p3) ∨ (p5 ∧ True)) ∨ (((p5 ∧ (((p3 → p3) → p4) → (False → p4))) → False) ∨ True)))) ∨ (p5 → p5)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_115626425306623989767997652479 : ((((((p2 ∨ p4) → p4) ∨ False) ∧ p1) ∨ ((((p5 ∨ (p4 ∧ p3)) ∧ (True → ((p1 ∧ p2) ∧ p5))) → p1) ∨ (p5 ∨ p3))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44989482396892436267853058532 : ((((p5 → False) ∧ ((p4 ∨ p5) ∧ ((p1 → (p3 → True)) ∧ (True → ((p3 → (p4 ∨ ((True ∧ (p5 ∧ p3)) ∧ p5))) ∧ p3))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160468955599448939062271640791 : ((((p1 ∨ p4) ∨ (((False ∧ (True → (p2 ∨ True))) ∧ p1) → (p4 ∨ p3))) → ((p4 ∨ p2) → False)) → (p1 ∨ ((True → p2) → (p2 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∨ p4) ∨ (((False ∧ (True → (p2 ∨ True))) ∧ p1) → (p4 ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h4
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p4 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710546125970012064104149296939 : ((((((True → p5) ∧ p1) ∧ (p5 ∧ p2)) ∧ ((p5 → p3) ∨ (p2 ∨ ((((p4 ∧ p1) → p3) ∧ p2) → (p5 ∧ ((p5 ∧ p3) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156816471423478480897928700344 : (((p2 ∨ (p1 ∨ (False ∧ (p5 ∧ ((p3 ∧ ((p2 → (p2 ∨ p4)) ∨ p1)) ∨ (p4 → False)))))) ∧ True) ∨ (((False ∧ (False ∧ p4)) ∧ p1) → p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699972290647924743358068944120 : ((((((False → (False ∧ p3)) ∧ True) ∨ (p1 ∨ (p5 ∧ (False → True)))) → (((p4 ∧ ((p5 → p1) ∨ ((p3 → p3) → p3))) → True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317744950748158421155486517615 : (p4 ∨ ((((p5 ∨ ((p3 ∨ (p5 ∨ (False ∨ ((p2 ∨ p3) → p2)))) ∧ True)) ∨ (True ∧ (p4 → p3))) ∧ (p5 ∨ (p2 ∧ (p1 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58928203260224266712908814923 : (((p1 ∧ p3) ∨ (((((p1 ∧ p2) ∧ p3) ∧ ((((p2 ∧ True) ∨ ((False ∧ False) ∧ p3)) ∧ p4) → True)) ∧ (False ∧ (p3 ∨ p4))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356015459360945887942641536519 : (p5 → (((p1 ∨ ((p5 ∧ False) ∧ (p5 ∧ ((p4 ∨ (((False ∧ (p4 ∧ p5)) ∧ True) ∨ p5)) ∨ False)))) ∨ p1) ∨ (p5 ∧ (p1 ∨ (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166874116093047173962201151724 : ((((True ∨ (((p3 → True) ∧ (p4 ∧ ((p5 ∧ True) → p5))) ∧ p1)) ∨ (False ∨ p2)) ∧ p1) → ((p5 ∨ (((p4 ∨ p3) ∧ p5) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248244707072120926401557189104 : ((p2 ∨ p1) ∨ (p5 ∨ (p2 → ((p1 ∧ ((p4 → (((((True ∨ p5) ∨ True) → p5) ∨ p5) ∧ p2)) ∧ p1)) ∨ (p2 ∨ (True ∧ (p2 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324013750161363059384468560433 : (p5 ∨ ((((p3 → True) ∧ (((p5 ∨ True) ∧ p5) ∨ (False ∧ (p3 ∧ p3)))) ∨ p4) → ((p1 → (((p4 ∨ (p4 ∧ False)) ∨ p1) → p4)) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h13



