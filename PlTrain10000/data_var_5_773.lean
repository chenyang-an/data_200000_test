variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350851280107068936041713356826 : (p4 → (((p3 → (True ∧ ((p2 ∨ p2) ∧ p1))) → ((False ∨ p3) ∨ (p3 → ((p4 ∧ (False ∨ p2)) ∧ (True ∧ (p4 ∨ True)))))) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216222391902298060397455544327 : ((p1 → ((p4 ∧ True) ∨ p2)) ∨ ((((((p4 → True) ∧ (True ∧ p2)) ∧ p4) ∨ (p5 → ((((p2 → p2) ∧ False) ∧ p5) → p1))) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → True) ∧ (True ∧ p2)) ∧ p4) ∨ (p5 → ((((p2 → p2) ∧ False) ∧ p5) → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114652157855716338458028047725 : (((((True ∨ (False → p4)) → (p2 ∨ (p4 ∧ p5))) ∧ (((False → p3) ∧ True) → p2)) ∨ (((p2 ∨ (p2 ∧ True)) → True) → False)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223353069161215501017580843747 : ((True ∨ (p5 ∧ p1)) ∧ ((p4 ∨ (((p5 ∨ ((((p3 ∧ p1) ∨ p3) ∨ (p1 ∨ True)) ∧ (p3 → p1))) ∨ p5) ∨ (p1 → p1))) ∨ (p2 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_664081041904380763689195347843 : ((((True ∨ (((((p3 ∨ ((True → (p5 ∧ False)) ∧ p4)) → p4) ∨ (p4 → p1)) ∨ ((False ∧ p5) → p4)) → (True → True))) → (p5 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687582292305932222218561709244 : (((((((p3 ∧ (((p3 ∨ False) ∨ (p2 → p1)) → p4)) → p1) ∨ (True → p5)) → True) ∧ (p3 ∨ (p1 → (True → ((p1 → p5) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58779685392332615782605750141 : (((p4 → p4) ∧ ((p4 ∨ (p1 ∨ False)) ∨ (((p3 → p3) ∧ ((p5 ∨ (((p5 ∨ p4) ∧ (p5 ∨ (True ∨ True))) ∧ False)) ∨ True)) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780285191132058197079809102214 : (((p2 ∨ (((((p2 ∧ p5) ∨ True) ∧ (False → (p1 ∨ p2))) → (True ∧ (False ∨ ((p2 ∨ p3) ∨ p2)))) ∧ ((p1 ∧ p2) → (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172308437587588067167301614686 : ((((False → p4) ∨ (p4 → (False → (False → p5)))) → (((p2 ∨ p4) ∧ p1) ∨ p1)) ∨ ((False ∧ False) → ((False ∧ p3) ∨ ((p1 → False) → p5)))) := by
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
theorem thm_5_vars_115066486160367012032961884679 : ((((True ∨ ((p4 ∨ p1) → p5)) → (p5 → (p4 ∧ (p3 → True)))) ∨ (True ∧ (False → ((p3 → p2) ∧ ((p5 ∨ False) ∨ False))))) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319291602137857309007736487491 : (p4 ∨ ((p2 → (((((((p4 ∧ False) → p5) ∧ True) ∧ p5) → (p1 ∧ p5)) ∨ p1) ∨ p5)) ∨ (p2 → ((p2 ∧ True) ∨ ((p3 ∧ p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38479939998567739615099482592 : (((((((p2 → p1) → p5) ∧ (p1 → True)) ∨ (p2 ∨ (p4 ∧ p4))) ∧ (((p1 → (p4 ∧ p3)) ∨ False) ∧ ((p5 ∧ p3) ∨ p4))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184392767704731547675096373479 : (((p4 → ((((p3 ∧ p3) ∧ False) ∧ False) ∨ (p2 ∨ p5))) → False) ∨ ((p4 ∨ ((True → (((p4 ∨ (p1 ∨ False)) ∨ p4) ∨ True)) ∨ p5)) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50460277028724142279268546951 : (((p5 ∨ (((p3 ∧ (p1 ∨ ((((p3 → p4) ∨ p4) ∨ False) ∧ ((p4 ∨ p1) ∧ True)))) → p2) ∧ p3)) ∨ (((p2 ∧ p3) ∧ p1) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134053695924749518680469922196 : ((((p2 ∨ (((p5 → (p4 ∨ p4)) → (((p3 ∨ (True ∨ p2)) ∨ ((p1 → p1) ∧ p1)) → p5)) → p2)) ∨ True) ∨ p2) ∨ (p1 ∨ (p3 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58841159522132197948012933721 : (((True ∧ p1) ∨ ((((True ∨ (p5 → p2)) ∧ p5) ∨ True) → ((p3 → ((p1 → (False ∨ (p5 ∧ ((True ∧ True) → p3)))) ∧ False)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42740200383898083888229247002 : (((True → (((((False ∧ (True ∧ p4)) ∧ (p4 ∧ (p4 ∧ False))) ∨ True) ∨ p3) ∧ ((p5 → p1) ∧ (True → (p1 ∨ (True ∨ p2)))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241842900012710334640851043114 : ((p1 → p1) ∧ ((p3 ∨ (p3 ∧ (p4 ∧ ((p2 ∧ ((p3 → p3) → p5)) ∧ True)))) ∨ (((False → p3) → (True ∨ (p2 ∨ p3))) ∨ (p3 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617263967899154589135540094971 : (((((p5 ∨ ((p3 ∧ (False ∧ (p4 ∨ p3))) ∨ p2)) ∨ (((True → ((p1 ∧ p4) ∨ p4)) ∨ False) ∧ ((p5 ∨ (True → p4)) ∧ p4))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42721221476163385220616257455 : (((p5 ∨ (p4 → ((False → p5) → (p2 ∧ ((p3 → (p2 ∨ (((p3 → ((p2 ∨ p4) ∧ p1)) ∧ p1) ∧ True))) ∨ (p1 ∨ True)))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41630876531945479156848970720 : (((((p1 → False) ∨ (((p4 ∨ p3) → p5) → p4)) → (((False → True) ∨ p3) ∧ (((p4 → p2) → p5) ∨ ((p2 ∧ False) → p2)))) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246581152174915590002804630490 : ((p5 ∧ p2) ∨ ((p4 → (True → ((p3 → ((p5 ∧ p5) ∨ p1)) → p3))) ∨ (((p3 ∧ (p5 ∨ (((True ∧ True) ∧ False) → p4))) ∧ False) → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214997189026497056088040851108 : (((True ∨ True) → (p2 ∨ p5)) ∨ ((p4 → p5) ∨ (True ∨ (False ∨ ((((False ∧ ((p1 ∨ (p1 ∨ p3)) ∧ p4)) → p3) ∨ p5) → (False ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345620879910225422998325408491 : (p3 → ((True ∧ ((p3 → (((False ∧ p4) ∧ (p4 ∨ True)) ∨ (p1 ∨ (((p4 ∨ p2) ∨ (p5 ∧ p4)) ∧ p4)))) → ((p5 ∨ p5) ∨ False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213108487205496638884555597825 : ((((p3 ∨ True) ∧ p4) ∧ p4) ∨ (p4 ∨ (((p4 ∨ p2) ∨ ((p2 ∨ ((((p1 ∨ p2) → p5) ∨ p2) → (False ∨ p3))) → True)) ∨ (p4 ∧ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53844865911674178819012912405 : (((((p3 → (p3 → p4)) ∨ p1) → (True ∧ (p4 ∨ False))) ∨ (((((p2 → (p2 ∨ p4)) ∨ True) ∧ p5) → ((p5 ∧ p2) ∨ p4)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307667638366587672576567095046 : (p1 ∨ (p2 → (((p5 → ((((p3 → p1) ∨ (p5 → p1)) ∨ p4) ∧ p2)) ∨ (((p5 → True) ∧ p2) → ((p5 ∧ (False ∧ False)) ∨ p2))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160670213078504160844458789836 : (((p4 → (((((p4 → p3) ∧ p4) ∧ False) → p4) ∨ p1)) → (p5 ∧ ((p3 → p5) → (p1 ∧ p1)))) → (p5 → (True ∧ ((p3 ∧ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175058116379215411233255416711 : ((p2 ∧ (True ∧ (False ∨ (p2 → ((p2 → False) ∧ (True → ((False ∧ p1) ∨ True))))))) → ((((p3 → ((False ∧ False) → p4)) → p5) ∧ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183900410741457201346437185079 : ((((p3 ∨ p5) ∨ ((p1 ∧ ((p1 → False) → p1)) ∧ p5)) ∧ True) ∨ ((p5 ∧ ((p5 ∨ ((p3 ∨ p2) ∧ (p2 → (p4 ∨ p5)))) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157216961628241563754911514449 : ((((p2 → ((p3 ∨ ((p5 → ((p3 ∧ p1) → p1)) ∧ True)) ∨ p5)) ∧ (p1 ∨ (p1 ∨ p1))) → p2) ∨ (((p4 → True) ∨ p5) ∧ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183039287985262312428308163819 : (((p3 ∨ True) ∨ ((((p5 ∧ p2) ∧ p1) ∧ p3) ∧ (True ∨ p1))) ∧ ((((False ∨ p5) ∨ p2) ∨ (((True ∨ p1) ∧ p4) ∨ (True → True))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_166434082206490358130879919541 : ((p1 ∨ (p3 ∨ (p2 ∨ ((p5 → ((p3 ∧ (((p5 → p2) ∧ p2) → p1)) ∨ p1)) ∨ p1)))) ∨ ((False ∧ True) → (p5 ∧ (True ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134141057939954167222735979712 : ((((((((((p4 ∧ p4) → p3) ∧ p4) ∧ (p5 ∧ (p5 ∨ False))) ∧ False) ∧ p1) ∧ p5) ∧ (p2 → (p4 ∨ p3))) ∨ p3) ∨ ((p3 ∧ p4) → p4)) := by
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
theorem thm_5_vars_167808429173165879705682037605 : ((((p4 ∨ (((True → p3) → p2) ∨ False)) ∧ (p5 ∨ p2)) ∧ ((p5 ∧ (p3 ∧ p3)) ∧ p4)) → (((p2 ∧ ((True ∧ True) ∨ p5)) ∧ p4) ∨ p5)) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h3.left
        let h25 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h3.left
        let h32 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h33 := h31.left
        let h34 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h37 =>
      -- False on the left can always be used.
      apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616434499258187337179677425326 : ((((((((p2 → (False ∧ (p2 → p3))) ∧ p5) → p5) ∨ (False → p5)) → ((p5 ∧ ((((True ∨ p2) → False) → False) → p5)) ∨ p3)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116642418424846342401613106477 : (((p2 → p2) ∧ (p2 ∨ (p5 ∨ (False ∨ (((True ∨ ((p1 ∨ p4) → True)) ∧ p2) → (((p5 ∧ (True ∨ p4)) ∨ p4) ∨ True)))))) ∨ (p2 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118233748431431023063021224778 : ((p1 ∨ ((((((True ∧ True) → (p5 ∧ p5)) ∨ p3) ∨ p5) ∨ (p3 → (p3 → ((p3 ∨ ((p4 ∨ p5) ∧ p3)) → True)))) → p4)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610827203185952998238953895873 : (((((((p3 → p3) ∨ ((p3 ∨ ((p4 ∧ p2) ∧ p4)) ∧ (p1 ∨ (p4 → p3)))) ∧ ((False ∨ p1) ∨ ((p4 → False) ∧ True))) → p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_139549142466513092198901223748 : ((((p1 ∨ (True ∧ (((p1 ∨ (p3 → (((p1 ∧ (True ∨ p2)) → p5) → True))) → True) ∧ p3))) ∨ (True ∧ True)) → False) → ((p4 → p1) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ (True ∧ (((p1 ∨ (p3 → (((p1 ∧ (True ∨ p2)) → p5) → True))) → True) ∧ p3))) ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∨ (True ∧ (((p1 ∨ (p3 → (((p1 ∧ (True ∨ p2)) → p5) → True))) → True) ∧ p3))) ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65272600904375683702992207127 : ((p3 ∨ ((p2 → (p1 ∨ ((((p5 ∧ ((p2 ∧ False) ∨ (((p5 → False) ∧ (p4 ∨ p3)) ∨ (p5 ∧ p2)))) ∨ p3) → p1) ∧ p1))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48393526397095123760042825102 : (((False → (((True ∧ False) ∧ False) ∨ (p3 ∨ (((True ∨ p2) ∨ ((p2 ∧ False) ∨ (p4 ∧ (p2 ∧ (p1 ∨ p1))))) → p2)))) → (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737545591610139901504435749824 : ((((p5 → False) ∧ (p3 ∧ ((False → (p1 ∨ (p5 ∧ p5))) ∧ (False ∧ ((((p5 ∨ p2) ∧ p2) → ((False ∨ p1) ∧ (p2 → p3))) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_526647904968835499535221732 : (((((False ∨ (p1 ∧ ((p4 → (((p3 ∨ p1) ∧ (((p1 → (p1 → p4)) ∨ True) → p3)) ∧ p3)) ∨ p5))) ∨ True) ∧ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646026144430195884133403617769 : ((((True → ((True ∨ False) ∧ (False ∨ (((((p5 ∧ p3) ∧ (True → ((p5 → p3) → p5))) → (False → (p3 ∧ p5))) ∧ False) → p3)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207958581999730708163457474284 : (((p5 → (p5 ∧ p4)) ∧ (p3 ∧ True)) → ((((p4 ∧ True) ∨ p5) ∧ (p5 ∨ ((p2 ∧ p3) → (p1 → (p5 ∧ False))))) ∨ (True → (p5 → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759938271349986934277746536639 : (((p2 ∧ ((True ∨ ((p1 → (p4 ∧ True)) → False)) → (((True ∧ (p4 → True)) ∧ (((p1 → ((p4 ∨ p2) → p2)) ∨ p3) → p5)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165684135568123262337368797404 : (((((p4 ∨ p3) ∧ p3) ∨ (p2 ∨ p2)) → (((p3 ∨ ((False → p4) ∧ True)) → p3) ∨ True)) ∨ (p5 ∨ (p5 ∨ (((p5 ∨ False) ∨ p1) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
theorem thm_5_vars_40539966758152619950797477156 : ((((p4 ∨ ((False ∨ (False ∨ (((p2 → (p4 ∧ True)) → (p2 → (((p5 ∧ True) → (p3 → False)) → p3))) → p5))) ∧ True)) ∨ p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647819615707394073702112180078 : ((((((p2 ∨ (False ∨ (True ∧ (((((p5 ∨ True) → p3) ∧ p4) → p2) → ((True ∧ (p3 → p5)) ∧ False))))) ∧ p3) ∧ p2) ∧ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49019541163312839355587016535 : ((((((p3 → (False ∧ (p5 → p2))) → ((False ∧ (p3 ∧ (False → False))) ∧ True)) ∧ ((p1 ∨ p4) → p3)) → p4) ∨ (False ∨ (False → p4))) ∨ p1) := by
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
theorem thm_5_vars_260657999134034768477324632511 : ((p3 → p3) → (((((p1 ∧ (((p4 → p1) ∧ (p4 → True)) ∨ (p2 ∧ True))) ∨ ((p2 → p3) ∧ (p5 ∧ p5))) → False) → p3) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48087574837120703607011406779 : (((((True → (p2 ∧ False)) ∨ (True ∨ p2)) → ((True ∧ p4) ∧ ((p2 ∨ p3) ∧ ((p4 ∧ ((p3 ∧ True) ∧ p5)) ∧ p2)))) → (True ∧ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p2 ∧ False)) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825902826273111175398012248591 : (((((p3 ∧ p4) ∨ (True → ((((((True ∨ (p3 ∧ (p5 → (((True ∨ p4) ∧ p4) ∨ p3)))) → True) ∨ True) ∨ p4) → p1) → p4))) ∧ p1) → p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (((((True ∨ (p3 ∧ (p5 → (((True ∨ p4) ∧ p4) ∨ p3)))) → True) ∨ True) ∨ p4) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h16 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152485708066715858405667966667 : ((((p3 ∧ p4) ∨ p3) ∨ (((((False ∧ (p5 ∨ (p5 → ((p4 ∧ p2) ∨ True)))) ∨ p3) ∨ False) ∧ p5) → p5)) → (p1 ∨ (p5 → (p4 ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810301896800889102929600097439 : (((p5 → ((p1 ∨ (p1 ∧ (((p3 → p3) → ((False ∧ False) ∧ p2)) ∧ False))) ∨ (p4 → ((False ∨ ((p5 → p5) ∨ True)) ∧ (p4 → p5))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54291861466672543854923181413 : ((((False ∨ p1) ∧ (p2 ∨ ((p4 ∨ p1) ∧ p2))) ∧ (((((p2 ∨ (p4 → True)) ∨ p4) → (False ∧ p5)) ∧ (p5 → p3)) → (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317869311970396956763941776369 : (p4 ∨ (((True ∧ True) → (((False ∨ (p4 ∨ (False ∨ ((((p4 → p4) → p2) ∨ ((p3 ∧ p2) → (True ∧ p3))) ∧ p3)))) ∧ p5) ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_135481187548620194286367377689 : (((((p4 → p1) → (p1 → p2)) ∧ (((True ∧ (p4 ∧ True)) ∨ p2) → (p5 ∨ (True → p5)))) → (p1 ∨ (p2 → True))) ∨ (p4 → (p4 ∧ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49321179758600004007793959877 : (((p3 ∨ (p1 ∧ (p5 → (((p4 → p5) → (((p2 ∧ (p2 → False)) → (p2 → (p3 ∨ True))) ∨ p1)) → p2)))) ∨ (p4 ∨ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113492059239529150690846794094 : ((((((p2 → (p5 ∧ ((False ∨ p5) ∨ False))) ∧ ((False ∧ (False ∨ p5)) → p4)) → False) ∧ (p2 → (p2 ∧ p4))) ∨ (p5 ∨ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259514917363774061817095334317 : ((False → p5) → ((((((True ∧ (True ∨ (p1 → p2))) ∧ p2) → p3) ∨ False) ∨ True) ∨ (p1 → (p4 ∨ (p3 ∧ (((True ∨ p2) ∨ p2) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178395028399038343498452143857 : (((((False → (False ∨ p2)) ∧ p3) → (True ∧ (False ∧ p4))) → (p2 ∧ p4)) ∨ ((True ∧ ((((p1 ∧ (p5 ∨ p5)) ∨ p2) ∨ False) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263717441683834469937296126097 : (True ∧ (((True ∨ ((p1 ∨ p1) → (((True ∨ p3) ∨ p4) ∨ (((False ∨ False) ∨ p5) ∨ False)))) ∧ p3) → ((((p2 → p4) → p5) ∧ p5) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137037406477276902249749895099 : (((True → True) → (((p2 → p5) ∨ ((((((p4 ∨ p1) → p3) ∨ (p1 ∧ False)) ∧ (p2 → False)) ∧ False) ∧ True)) ∨ p2)) ∨ (p3 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166166263271261428974235335908 : ((False ∧ ((p1 ∧ False) ∧ ((p3 → ((False → ((p1 ∧ p5) → (p4 ∨ p1))) ∧ p4)) → p3))) ∨ (p2 → (p3 ∨ (((p2 ∧ p2) → p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115562914202298980555458845877 : (((((p2 ∧ p4) → (p1 ∧ p5)) ∨ p5) ∧ ((p1 ∨ False) ∨ (p2 ∧ (p3 ∨ (p1 ∧ ((((True → False) ∨ p4) → False) → False)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113554248851983114148999583793 : ((((p3 → (p1 → False)) → (p1 → ((p5 ∨ (p2 ∧ True)) → (p4 ∧ (((p5 → (p2 ∨ p2)) ∨ p5) → p5))))) ∨ (False → p2)) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317581650186423036082863456780 : (p4 ∨ (((((p4 ∨ (False ∧ ((False ∨ (((False ∨ p5) ∨ p5) ∧ ((p1 → (p4 ∨ (p5 → p5))) → p5))) ∧ False))) → p5) → p5) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785541232671656046292406042973 : (((p4 ∨ ((p1 ∨ (((True ∨ p3) → (p3 → (p5 ∨ ((p4 ∧ p4) ∨ p2)))) ∨ ((False ∧ (p5 ∨ (p1 ∧ p5))) → (False ∧ p3)))) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675407625944897690584714712157 : ((((((False → (p3 ∧ (p1 ∧ (p5 → p3)))) → (p4 ∨ (True ∨ (p1 → (p2 ∧ (p3 ∨ p4)))))) → False) ∧ (p1 ∧ ((False ∨ p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213853566151875913177103770505 : (((False ∨ (p5 ∧ p2)) ∨ p2) ∨ (p1 ∨ ((p1 ∨ p1) → (p5 → ((True ∧ (((p3 ∨ p3) ∨ p4) ∧ True)) ∨ (p3 ∨ (p1 ∧ (False → False)))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618499253515749150248389187901 : ((((((p1 ∨ p2) ∧ (p5 → p2)) → ((((p1 ∧ (False ∨ (p3 → (p2 → True)))) ∨ (True ∧ True)) → (p1 ∧ p2)) → (p5 ∨ p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744338093889094431827739967888 : ((((p1 ∧ p5) → (((p5 ∨ (p4 ∧ (p1 ∨ (False → p2)))) ∧ (p5 ∨ ((False ∨ ((True ∧ p1) ∧ (p1 → p4))) → True))) → (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157974463149022404762900334130 : (((p3 ∨ (((p2 ∧ p5) ∨ (p5 ∧ p4)) ∧ p2)) ∨ ((p1 ∧ ((False ∨ p5) ∨ p4)) → (p4 ∨ False))) ∨ (False → ((p5 → (p2 ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114963828406286088690910627744 : (((True → (((True ∧ p2) ∧ ((((True ∧ True) ∧ True) ∧ True) ∧ p5)) ∧ p3)) → (p5 → (((True ∧ (p4 ∨ p5)) → False) ∨ p1))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343506465227179412278531569959 : (p2 → ((p1 ∧ p1) → ((p5 ∧ False) ∨ ((p1 ∧ (True ∧ (False ∧ (((((p4 ∨ p5) → p5) ∨ False) ∧ True) ∧ False)))) ∨ (False ∨ (True ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
theorem thm_5_vars_254213039019825611214451510553 : ((p2 ∧ p2) → ((p4 → (p3 ∨ ((((p5 → p1) ∨ ((p2 ∧ False) ∨ p1)) ∧ ((True ∧ ((False ∧ p3) → True)) → False)) ∨ (True → True)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623899547232135725363971355617 : ((((p1 ∨ (p1 → (p4 ∨ (p5 → (p1 → ((((p4 ∧ p5) ∧ ((False ∧ (True → p5)) ∨ p5)) ∨ p1) ∧ (False ∨ (p5 → p5)))))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134533675248871501713083049357 : (((((((p1 ∨ False) ∨ p2) ∧ (p4 ∧ (p2 → (((p1 → p2) → p2) ∧ (p1 ∧ (True ∨ p3)))))) → p1) → p3) → p2) ∨ (p4 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156663255721190168917417156099 : ((((p1 ∨ (False ∨ (p1 ∨ (p3 ∨ ((p1 ∧ (True ∨ (p2 ∧ p1))) ∨ (p1 → p2)))))) → p1) ∧ False) ∨ (True ∨ (p3 ∧ (p4 ∨ (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134856963189335129009914793598 : (((True → ((True ∨ (((p2 ∨ (p4 ∧ p4)) → (True ∧ (p5 → p3))) ∨ (p4 ∧ (False ∨ p3)))) ∧ (p1 ∧ p5))) → p5) ∨ ((p2 → p4) → p3)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117434089961633117020910859736 : ((p1 ∧ ((False ∨ ((p1 → (False → ((p5 ∧ p2) → p5))) → ((p1 ∨ p3) → p2))) → (p2 ∧ (True → (p1 ∨ (False ∨ p2)))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679222760340695616872153064304 : ((((True → (((((p1 ∨ True) ∧ ((p3 ∧ p1) ∨ ((p3 ∧ p2) ∨ p5))) → p1) ∨ (p5 ∧ p4)) → p4)) ∨ (p5 ∨ ((True ∧ p5) ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_113534868923400375510725039931 : (((((p5 → p5) → (p1 ∧ (p2 ∧ p1))) → ((p2 → ((p2 ∨ p3) ∧ ((p4 ∧ (p3 → False)) → p5))) → p3)) ∨ (p5 → p5)) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42269037392002231685284482534 : (((p1 ∧ ((p3 ∨ ((p3 ∨ ((True ∨ (p3 ∨ p5)) → p3)) ∨ p3)) ∧ (True ∨ (p5 ∧ (((True → p5) ∨ (p4 → False)) ∨ p4))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47304911361731101040351457169 : (((((p2 ∧ True) ∧ p2) ∨ ((p5 ∧ (True ∨ (p2 ∧ (((p2 ∨ p3) ∧ p4) ∧ ((p1 → p3) ∧ p4))))) → (p3 ∨ p3))) ∨ (False → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670240287703226917247520122887 : (((((False ∨ (p4 ∨ (p1 ∨ False))) ∨ (p5 ∨ (((p3 → ((p1 ∨ p2) ∧ (p4 ∨ p5))) ∨ p5) ∧ (p1 ∧ p2)))) ∨ ((p1 → False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66117537674822564882262108917 : ((p5 ∨ ((True ∨ (p3 ∧ ((p2 ∧ p5) → ((False ∨ (p1 ∨ (p2 ∧ ((p1 → True) ∨ ((p1 → (p2 ∨ p1)) → p3))))) → p2)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588552529346405724660607542649 : ((((((True ∧ p2) → ((((((False ∨ p1) ∧ p2) ∧ True) ∨ (False ∨ (p1 ∧ p1))) ∧ (p1 → ((p3 ∨ p4) ∨ p1))) ∧ True)) ∨ p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707737537568333116186480651240 : (((((p5 ∨ False) → (((p1 → False) ∧ p3) ∨ False)) ∨ (((((p5 ∨ ((p4 → p2) → (p5 ∧ p3))) ∨ (p5 ∨ p3)) ∧ p5) ∧ p1) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_233850459769415861409407716421 : ((p4 ∨ (p3 ∧ False)) → (((False → ((p1 ∧ False) ∧ (((p5 ∨ p1) ∨ (p2 ∨ ((False → (p5 ∧ (p4 ∧ True))) ∨ p1))) ∨ p3))) → p5) ∨ p4)) := by
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
theorem thm_5_vars_192757150821195885713863410042 : (((True ∧ (p1 → ((False → p3) ∨ (p4 → p4)))) → p1) → (((p2 ∨ (p4 ∨ p4)) ∧ p1) ∨ ((p4 ∨ ((p3 ∨ p3) ∨ False)) ∨ (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707576361142717276717204324207 : (((((False ∧ p2) ∧ (True ∨ (p4 → (p3 ∨ p1)))) ∨ (((p2 ∨ p2) ∨ ((p2 → (False ∧ (True → False))) ∨ p1)) ∧ ((p2 ∧ p5) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46063338164756629947180464752 : (((((p4 ∧ ((p5 ∧ (p3 → ((p4 → p4) ∧ p5))) ∧ ((p3 → ((False ∧ (p3 ∨ True)) → p3)) ∧ p3))) ∨ True) ∨ p3) ∧ (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171292017906931443364532803348 : ((p5 → (p5 → ((p3 → ((False ∧ (p4 ∧ (p2 ∨ False))) ∨ p5)) ∨ (p5 ∧ p2)))) ∧ (p2 ∨ (((((True → p3) ∨ False) ∧ p3) ∧ True) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159094334734916259583528064547 : ((True → ((p4 ∨ (p3 ∨ ((p5 ∨ ((p5 ∧ p1) ∨ p4)) → p4))) → (((p4 ∨ p5) → p1) ∨ p2))) ∨ (p5 ∨ (((p2 ∧ False) ∧ p5) → False))) := by
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
theorem thm_5_vars_679402282375894406684582324587 : ((((p4 → (p5 → ((p4 ∧ ((p1 ∧ p2) ∨ ((p2 → ((True ∨ (p4 → False)) ∨ p4)) → p1))) ∨ p5))) ∨ ((p3 ∧ (p3 ∧ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184675566374382679775658537499 : (((p4 ∧ ((p3 ∧ (p4 ∨ True)) ∨ False)) ∨ (p3 ∨ (p1 → p5))) ∨ (p4 → (((((((p5 ∧ p2) ∧ p5) → p2) ∧ p1) ∨ p1) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149071750088511047235989454079 : ((((p5 ∨ p1) ∨ False) → ((p2 ∨ p4) ∨ (p2 ∨ ((True ∧ (p1 ∧ True)) ∨ (p4 → (True ∨ (True → False))))))) ∨ (p4 → ((p2 → p2) → False))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



