variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257208719765234133730329594951 : ((p2 ∨ p2) → ((True ∧ ((p5 ∧ (False → ((p3 → p3) ∨ p4))) → p3)) ∨ ((p2 ∨ (p1 ∨ p3)) ∨ (((p3 → p1) → p4) ∨ (p1 ∧ p5))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43192851447122970087630160815 : (((((p4 ∨ p2) → ((True ∧ (((p2 ∨ True) → (((p5 ∨ False) ∧ False) ∨ p5)) ∧ (True ∧ (p3 ∧ (p4 ∨ p2))))) ∧ p2)) ∧ p4) → p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230708742762540115657192746889 : (((p4 → p4) ∧ p2) → (((True → ((p2 ∧ (((p2 → p3) ∨ False) ∨ ((p5 ∧ (p3 ∧ p2)) → (True ∨ p5)))) ∨ (False → True))) → p5) ∨ p2)) := by
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
theorem thm_5_vars_50498580459595184657480843608 : (((((p1 → ((False ∧ True) → ((p5 ∨ (((p2 → True) ∨ (True ∧ False)) ∨ p2)) ∧ p3))) ∧ p4) ∧ p4) → (((p1 ∨ p3) ∨ False) ∨ True)) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37810195753639095381242491172 : ((((p3 ∧ (((((True ∧ (p5 ∧ p1)) → ((p2 → p4) → (p4 ∨ p3))) → (p3 ∨ p3)) ∧ ((p2 → p1) ∧ p5)) ∧ p5)) → p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138013655051936084805478666815 : ((True → ((((p5 → (p2 → ((True ∨ ((True ∨ p3) → p2)) ∧ (p3 ∨ (p5 → (p4 → True)))))) → p3) ∨ p3) ∨ True)) ∨ (False ∧ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588697575737423417237608746754 : (((((p2 ∧ ((p1 ∨ p3) → (False ∨ ((p1 ∧ (p2 ∨ ((p4 ∧ (p5 → (True → p5))) → (False → p1)))) ∨ (p1 ∧ p4))))) ∨ True) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134285925412862529533898284520 : ((((p1 ∨ p5) ∨ ((p1 ∧ p4) → (((p4 → ((p2 ∨ True) ∧ p2)) ∨ (p3 → p2)) ∨ ((p1 → p2) ∨ p4)))) ∨ True) ∨ ((True → p4) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49168373324968015107658814445 : ((((p3 → ((p3 → (p2 ∧ p2)) → False)) ∨ (p4 ∧ ((p1 ∨ p1) → ((p5 ∧ (p3 ∨ (p3 ∧ True))) ∧ p3)))) ∨ (p3 ∨ (False → p1))) ∨ p5) := by
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
theorem thm_5_vars_685744522199929830271502482663 : (((((((p1 → ((((p3 ∨ (p2 ∨ p1)) ∨ p1) ∨ (p3 ∨ p4)) ∧ p1)) → False) ∧ p2) → p5) → ((True ∨ p4) ∧ (p1 → (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354865570790912575551811139507 : (p5 → ((True ∧ (((p4 ∨ p1) ∧ ((((((p2 ∧ (((p1 → p2) ∨ p2) ∨ False)) ∨ False) → p5) → (p3 → False)) → p1) ∨ False)) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315022183961934579853779935861 : (p3 ∨ (((False ∧ p3) ∨ ((p1 ∨ (p2 → False)) ∨ True)) ∨ (p2 → ((((False ∧ True) → ((p1 ∧ (True ∧ (p2 ∧ p4))) ∨ p1)) ∧ p2) → p2)))) := by
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
theorem thm_5_vars_616802872801113161437436775907 : (((((p3 ∨ (((p1 → (p5 ∨ p1)) ∧ p1) ∧ (p2 ∨ p1))) ∨ (((p3 → p3) ∧ True) ∨ (False ∧ (p3 ∧ ((p5 → False) ∧ p5))))) ∨ p5) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257632625104271161918164197591 : ((p3 ∨ p2) → ((p4 ∨ (p5 ∨ (((p5 → p5) → (p3 → False)) ∨ (False ∨ False)))) ∨ ((((p5 ∨ (p3 ∧ p5)) ∧ (p5 ∨ p1)) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340182754004384312137144300259 : (p1 → (p4 → ((True ∧ p5) ∨ (((False → (p4 → p1)) ∧ p1) ∧ (((p5 ∨ False) ∨ (p3 ∨ False)) ∨ ((False → p1) ∨ (False ∨ (p3 → False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38158796266348740730747246857 : ((((((True → p5) → (((p2 ∧ (p1 ∨ ((((False ∧ True) ∧ p2) → p1) → p4))) ∧ p4) → p3)) → p2) ∨ (p5 → (True ∨ p5))) ∧ True) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336088600891842618280958248976 : (p1 → (((((p3 ∧ (p1 ∨ p4)) ∨ p5) → (((((p4 ∧ False) → p2) ∧ (False ∨ p3)) ∨ (p3 ∨ ((p2 ∧ p4) ∧ p1))) ∨ True)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65415700934249982798614710389 : ((p3 ∨ ((True ∨ (True → p3)) ∧ (((True ∨ False) ∨ ((p1 ∨ p1) ∨ p3)) ∧ (p1 → (False ∧ ((p2 ∨ (p5 → (True → False))) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67492638511493931808700711771 : ((p1 → (((((False ∨ p5) ∨ p4) ∧ (False ∨ p4)) → ((p4 → p4) ∧ False)) → (p4 ∨ (p5 → ((p4 → False) ∨ (p2 ∧ (False ∨ p2))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((False ∨ p5) ∨ p4) ∧ (False ∨ p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112795224745156016639546746139 : ((((((p5 ∧ True) → p2) ∨ (True ∧ p2)) ∧ ((p1 ∨ (p2 → p2)) ∧ (True ∧ (((p3 ∧ p3) ∨ p5) ∨ (p5 → p5))))) → False) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114025106937143026758620362660 : ((((p2 → (((p1 ∧ ((p3 ∨ p4) → (False ∨ p2))) ∨ (p5 ∨ False)) → ((p4 ∨ p5) → p3))) ∨ True) ∨ ((p1 ∧ False) → p2)) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672429043378087405884500995983 : ((((((p5 ∧ False) ∨ ((p1 ∨ (((p5 → ((p1 ∨ False) → (p3 ∧ (True ∨ True)))) ∨ p5) ∧ p3)) → False)) → p4) → (p3 ∨ (p2 → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_678741719522946744313949726258 : (((((False ∨ p1) → (((p5 ∨ p3) ∧ (p1 → p1)) → ((False ∨ ((p4 ∧ True) ∧ (p3 ∨ p1))) ∨ p1))) ∨ ((p1 ∧ (p3 → False)) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258807845322692754379283983474 : ((True → False) → (p1 ∨ (((((p4 ∧ ((p5 ∧ (p3 ∨ ((p3 → False) ∧ False))) ∧ ((p2 ∧ False) → (p4 ∨ p5)))) ∨ p1) → p5) ∧ p5) → False))) := by
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
theorem thm_5_vars_166440006337129621077495939644 : ((p2 ∨ ((((p2 ∨ p4) ∨ p1) ∧ (((p1 ∨ (False ∨ p1)) ∧ p1) ∨ (p3 ∨ False))) ∧ True)) ∨ ((False ∨ False) → (True ∨ ((p4 ∧ p5) ∧ p1)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159254786549166619596492131845 : ((p3 → (p2 ∧ (((p1 → p2) → ((p5 ∨ (p5 ∨ p3)) ∧ (p4 ∧ (p5 ∧ p5)))) ∧ (p1 → p3)))) ∨ (True ∨ ((p4 ∨ p1) → (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62771073876907525307759064330 : ((p4 ∧ (((False → ((False ∨ (((p1 ∧ (p5 ∨ ((p1 ∧ p1) ∨ p2))) → p1) → p3)) → p3)) ∧ (p5 → p2)) → (p5 ∨ (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781407656965167701390448260888 : (((p2 ∨ (p3 ∧ ((p4 ∨ ((p5 ∧ False) → (((p5 ∧ p5) → False) ∨ p2))) → ((p3 ∨ (p3 → (((p2 ∧ p5) → p4) ∧ p2))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166912395913657418437493423920 : ((((True ∧ ((p4 ∨ (False ∨ p1)) ∨ True)) → ((((p5 → p5) → True) ∨ p4) → p1)) ∧ p5) → ((True ∧ p1) ∨ ((p2 → (p3 ∨ p3)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ ((p4 ∨ (False ∨ p1)) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 → p5) → True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148055279109539607005954338211 : (((p2 ∨ ((((True → True) ∧ ((p4 ∨ p3) ∧ True)) → p4) ∧ ((p2 ∧ p3) ∨ (False ∨ p3)))) ∨ (True → p1)) ∨ ((p2 ∧ (p1 ∧ p3)) → p3)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90923732458280994807103703633 : (((True → False) ∧ (p4 → ((p4 → (p1 ∨ False)) ∨ (p2 ∧ (False → ((p1 ∨ (((p1 → (p3 → (False ∨ False))) → False) → p3)) ∨ p2)))))) → p1) := by
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
theorem thm_5_vars_784202307978508263726877541413 : (((p3 ∨ ((p5 → True) → ((((p4 → p5) ∨ ((p5 ∨ ((p1 ∨ True) ∧ (True ∧ p3))) → p1)) → (p1 ∨ (p1 → (p4 → False)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340739722174856852360812412480 : (p2 → ((((p3 ∧ (((((p5 ∧ (p4 ∧ p4)) → (((p2 → (p5 → True)) ∨ p2) → p3)) ∧ p2) ∧ p4) ∨ True)) ∧ (p1 ∧ p2)) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301049009826297484026128160865 : (False ∨ (((((p3 ∧ (p3 ∧ p2)) → p2) ∨ (p4 ∧ p3)) → p2) ∨ ((p4 ∧ (True ∨ ((p1 → True) → (p4 → ((p3 → True) → p3))))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171775442499031593092515204570 : (((((((p5 → ((p2 ∧ p4) ∧ p2)) ∨ p4) ∨ p5) ∧ p3) ∧ (True ∨ p1)) → p4) ∨ ((((p1 → p4) ∨ p4) ∨ p5) → (False → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59814650118366068382927941058 : (((p3 ∧ True) → ((False ∨ p2) ∨ (p2 → (((p2 → (p5 → (((True ∨ (p4 ∨ False)) → (p3 ∨ p3)) ∨ False))) → (p4 ∨ p5)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158756773113662109232874119596 : ((p4 ∧ (((((p5 → p1) ∨ False) → False) → ((p1 ∧ p4) ∨ p3)) ∧ ((p1 ∨ (p3 ∧ True)) → p2))) ∨ (((True ∧ p4) → p1) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354981319299749652067810198099 : (p5 → ((p5 → (False ∧ ((((((p4 ∨ True) ∧ (p3 ∨ p5)) → ((p1 ∧ p4) → False)) → (p5 → True)) ∨ True) → (p1 ∧ (p2 ∧ p2))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591939082135636590816557519332 : (((((((p5 ∨ p5) ∧ True) ∨ ((p4 ∨ p5) ∨ ((False ∨ True) → (p5 ∨ ((True ∨ (p1 → False)) → (p2 → p2)))))) ∨ (p2 ∧ p1)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346341528531263163029536643388 : (p3 → (((((True ∨ (True ∧ True)) ∨ (p2 ∧ p2)) → p1) ∨ ((((p1 → (((p3 ∨ p4) ∨ False) ∨ False)) ∨ p1) ∧ True) → False)) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234111632171118522119604617474 : ((True → (False ∨ p3)) → ((((p3 ∨ True) → p2) ∧ ((p2 → True) → ((((True → (p5 ∨ (p1 → True))) → (p2 → True)) ∧ p5) ∧ False))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177735173805287287862200851554 : ((((True ∧ (True ∧ p4)) ∧ ((((False ∨ p5) ∨ p2) ∨ p5) ∧ p4)) ∧ p5) ∨ ((p4 → (True → ((((p1 → True) → p5) ∨ p5) → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147283457689802073450161891861 : ((((p4 ∧ ((((p4 ∨ p1) ∧ (True → ((False ∨ (True ∨ p5)) ∧ p1))) ∧ p3) ∧ (True → p3))) ∨ p1) ∨ True) ∨ (True → (True ∨ (p4 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693585727435721109351558725326 : (((((p3 ∨ ((p5 ∨ (False ∨ p3)) ∨ (p1 ∨ ((p4 ∨ p5) ∨ p1)))) ∧ p4) ∨ ((True ∧ ((p3 → (True → p1)) → (False → True))) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744873362917055974781679674559 : ((((p3 ∧ p4) → (p1 → (p5 ∨ ((p3 ∧ (((False ∨ p5) ∨ ((p1 ∧ p3) ∨ p1)) ∧ (False ∧ ((False ∧ True) ∧ (p3 → p1))))) ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117925440734794476998740867418 : ((p5 ∧ ((True → (p4 ∧ p5)) ∨ ((p4 → ((p3 ∧ (p2 → (((p1 ∨ False) ∧ p2) ∧ p2))) ∨ p4)) ∨ (True → (True ∨ p2))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258436419828018180883302535136 : ((p5 ∨ p1) → (True ∧ (((((((((p4 ∧ (True ∧ p1)) ∧ p5) → p2) → p3) ∧ True) ∧ p2) → False) ∧ p3) ∨ (((p4 → p2) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113067597990226374837196389139 : (((p3 ∨ (((p1 → ((((True ∧ (p1 → p5)) ∨ (p1 ∧ (p2 → p4))) ∧ (False ∧ p5)) ∧ (p2 ∧ p3))) ∧ p5) → p5)) → p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171147928409124163162223810605 : ((p1 → ((p5 ∨ (((True ∨ (p5 ∨ (p4 ∨ p1))) ∧ (p4 → False)) → False)) ∨ p1)) ∧ ((((p3 ∧ True) ∧ p2) ∧ p2) ∨ ((p1 ∨ True) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_135523041078273956270800097998 : (((((p1 ∨ (((p4 → (True ∨ p3)) ∨ p4) ∨ p2)) → ((p2 → p3) ∨ p5)) ∨ p4) ∧ (False → (p1 ∧ (p5 ∧ p5)))) ∨ ((True → p4) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193292650042806281667768000135 : ((((p2 ∧ p1) → p4) ∨ ((p5 → p1) → (p5 ∧ True))) → ((p1 → True) → ((((True ∧ False) ∧ ((True ∧ p4) ∨ (True ∨ p2))) ∧ p3) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306233732844476685002123983376 : (p1 ∨ (((p2 ∨ True) → p3) → ((((p1 ∧ p4) ∧ p1) ∧ (p4 ∨ p1)) ∨ (True → (((p4 ∧ p3) ∧ False) ∨ (((False ∨ p2) ∧ p1) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193832378923832838057056075328 : ((p5 ∧ (True → (((p5 ∨ p1) ∧ p3) ∨ (p3 ∨ p1)))) → (((p5 → False) ∨ (((p3 ∨ ((p1 → p2) → False)) → (p5 ∨ p3)) ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256286240790938895800723833065 : ((False ∨ p1) → (((p3 ∨ p1) → (p5 ∨ ((False → (((True ∨ (True ∨ (p1 → p4))) → (p5 ∧ True)) → True)) → (p4 ∨ p4)))) ∨ (p3 ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209448331348132558114630355422 : ((p2 → (p4 ∨ (p5 ∧ (p5 ∧ p3)))) → ((p2 → (p2 ∧ (p1 → (p3 ∨ (p4 ∧ ((p1 ∨ (False ∨ p3)) ∨ True)))))) ∧ (True ∨ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58395041984000434079308061610 : (((p2 ∨ True) ∧ ((((((p5 ∨ ((True → p4) ∨ True)) → ((True → (p4 → p3)) → p5)) ∧ False) ∧ (p5 → p2)) → (False → False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785548780660272313473074613992 : (((p4 ∨ ((p3 ∨ ((False ∧ (((True → False) ∧ p5) ∨ True)) ∨ ((p3 → p5) → (((False ∧ p4) ∨ (False ∨ p4)) ∨ (p5 ∨ p4))))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_199501393264404421010169961080 : (((p1 → (((p4 ∧ p2) ∨ p2) ∨ p3)) ∨ False) → ((True ∧ ((False ∧ p1) ∨ ((True ∧ (((False → (True → p4)) → p2) ∨ p3)) ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_655893317885255267793328025715 : (((((True → ((((((p3 → (((p5 ∨ p4) ∨ True) ∨ p5)) ∨ False) ∨ p4) ∧ p5) ∨ p3) ∨ p2)) → (p2 ∧ (p1 ∨ p1))) ∨ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245707679308467971734628928817 : ((p3 ∧ p2) ∨ (((p5 → (((p2 ∧ ((p1 → (p1 ∨ False)) → True)) ∨ p2) ∧ (p1 → (p2 → p3)))) ∧ ((p4 ∨ (p1 ∧ False)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117732795008703825570804124684 : ((p3 ∧ (p5 → (((((((False ∨ p1) → p5) ∨ True) → p1) ∨ (((False → p2) ∧ p2) ∧ False)) → p4) → (p2 ∨ (p3 → True))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326262932709146496940344416717 : (p5 ∨ (p3 → (False ∨ ((False ∨ p5) ∨ ((p5 ∨ (((False ∧ (((((p3 → False) ∨ False) → p2) ∧ True) ∨ p5)) ∨ True) ∨ (p3 → p3))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119492502782559834860193646370 : ((p4 → (p5 ∨ ((((p4 ∨ (p1 ∨ ((True ∨ p3) ∨ p1))) ∨ True) ∨ (False ∧ ((p5 ∧ (p4 ∧ False)) ∧ (False ∨ True)))) ∧ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60280424970137717694642368691 : (((False → p5) → ((True ∨ ((True ∨ ((False → p3) ∧ True)) → (False ∧ p1))) → (((p5 → ((True ∧ (p4 ∨ True)) ∧ True)) → False) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265515549607161755575352922037 : (True ∧ (False ∨ ((p1 ∨ ((p1 ∨ ((((p5 → False) ∨ ((False → p1) ∧ ((True ∨ True) → p1))) → p4) ∨ (p4 ∨ (True ∨ True)))) ∨ p3)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63076520721692122724892323399 : ((p5 ∧ (((p3 ∧ (((True ∧ (p5 ∧ p4)) ∨ ((p1 → (p3 → (p5 → p4))) ∨ (p4 ∧ (p5 ∧ p4)))) ∨ (p4 ∨ p5))) ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346621260744321755642446281891 : (p3 → ((((True ∨ p5) ∧ p4) ∧ (p1 → (p4 ∧ (p5 ∨ ((True → True) ∧ ((((p5 ∨ False) ∧ p3) ∨ p4) ∧ p4)))))) ∨ ((p3 ∧ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174509716601601539181073900961 : ((((p4 → p3) → ((p1 ∨ p2) → p3)) ∨ ((p3 ∧ p3) → ((p4 → p3) → p5))) → ((p3 ∨ (((True ∨ p5) ∧ (p3 ∨ True)) ∨ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165940580446729026675018395377 : (((False ∨ p3) ∧ ((p5 ∧ (True ∨ (((p5 ∧ p1) ∨ (False → p5)) → (False ∨ True)))) → False)) ∨ (p1 → (p3 ∨ ((p2 ∧ p5) → (p4 → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112941125549464411344197019628 : ((((p3 → True) → ((True ∨ ((p1 ∨ (p5 → (((p5 ∨ (p5 ∨ p4)) ∧ (p1 ∧ p5)) → p1))) → p4)) ∧ (False ∧ p5))) → False) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156957922294648181493632576970 : (((((False → (p2 ∨ (p2 ∨ p3))) → ((p5 ∧ p5) ∨ (p1 ∧ p5))) ∨ (p2 → (p5 ∧ p2))) ∨ False) ∨ (p1 ∨ (p3 → (True ∨ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67794712387878792766703816381 : ((p2 → ((((((p2 ∨ (p4 → p5)) ∨ False) → (False ∨ (p2 → p1))) → (p1 ∧ (p5 → (p5 ∨ ((False ∨ p1) → p1))))) → p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92488186561604513651735960149 : (((p4 ∨ True) → (((((p4 ∨ ((p1 ∧ p3) ∧ (True → True))) ∧ True) ∨ ((p1 ∨ p4) ∨ (False → (False ∧ (False → p1))))) ∨ p5) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 ∨ ((p1 ∧ p3) ∧ (True → True))) ∧ True) ∨ ((p1 ∨ p4) ∨ (False → (False ∧ (False → p1))))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321476318330496747669051425296 : (p4 ∨ (p1 → (((p3 ∧ (True ∧ ((p2 → True) ∨ p3))) ∨ ((True ∧ False) ∨ (p3 ∨ ((p4 ∨ True) → ((p2 → True) ∧ (p5 → p3)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757011582687032453760044868831 : (((p1 ∧ (((p2 → (p1 ∧ True)) → p2) ∨ ((((p3 → p1) ∨ (((p2 ∧ ((p4 ∧ p3) ∧ (p4 → p1))) ∨ p4) ∨ True)) ∧ True) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48193664370866862993860798902 : ((((False → False) ∨ (((p1 ∨ (((((p2 ∨ p4) → False) → (p2 ∧ True)) → (p4 ∨ (p4 ∧ p3))) → p3)) ∧ p5) ∨ False)) → (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731879572356856751080551962223 : ((((p4 → (p3 → p4)) → ((((p4 ∧ p5) ∧ (p1 → False)) ∨ p5) ∨ (((p4 ∨ (p2 → p1)) ∨ p2) ∨ (True ∧ ((True → p2) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144056380703734115720804100973 : (((True → (p3 → ((((p4 ∧ p5) ∨ (((p5 ∧ p3) ∧ p2) ∨ p2)) ∧ p1) ∨ ((True ∨ p3) ∧ True)))) ∨ True) ∧ ((p4 ∧ (False ∧ p1)) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751962871071773438344171042572 : (((True ∧ (p4 ∨ ((((p2 → p2) ∧ (p5 ∨ (p2 → ((p4 → (p2 → False)) → p3)))) ∨ p3) → (p4 → (((p1 → p5) ∨ True) ∨ False))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218499640777124934777572081527 : (((p1 ∨ p5) → (True ∧ p5)) → (((p5 → ((p3 ∨ p5) ∨ p2)) → p5) ∨ ((p1 ∧ (p5 ∧ p1)) ∨ ((False ∧ ((p1 ∨ False) ∧ p4)) → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118157187163933943350709020651 : ((False ∨ (((p4 ∨ (p3 → True)) ∧ p1) → ((p1 → (p4 ∨ (True ∧ ((p1 ∧ (p3 ∧ ((p2 → p2) ∧ p2))) ∧ p1)))) ∨ True))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_136333396605890897942881851244 : ((((False → p3) → (p5 ∧ p2)) ∧ (((((p3 → p4) ∧ (False ∧ p2)) → ((p1 ∧ p5) → p4)) → (p3 → p5)) ∧ p2)) ∨ (False → (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172879592791902806824857560809 : ((p1 ∧ (((p3 ∧ (False ∨ p5)) ∨ p3) ∧ (p5 → ((p5 → (p4 ∧ p2)) → p4)))) ∨ ((True → ((True ∨ False) ∨ (p2 → (p5 ∧ p5)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311034434322344137493484591545 : (p2 ∨ ((p2 ∧ p3) ∨ (p3 ∨ (((False ∨ (p4 → (p3 ∧ True))) → (((p4 ∨ p1) → (((p2 ∨ (p4 ∨ p5)) ∧ p3) → p1)) → False)) ∨ True)))) := by
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
theorem thm_5_vars_686233953735890585805956363334 : (((((p2 ∨ (False → ((((p5 ∧ p3) → p3) ∧ True) ∧ False))) → (p4 → (True ∧ (p1 ∨ p3)))) → (False ∧ (((True ∨ False) ∧ True) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56861043799758395897459589613 : (((False ∧ (p5 ∨ p2)) ∧ ((p1 ∧ (((((p5 → p1) ∨ p2) ∧ p2) ∧ (((True ∨ (p4 ∧ False)) ∨ p5) ∨ p2)) ∨ (p5 ∨ p2))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209370193153263604124557532519 : ((p1 → (((p4 ∨ False) ∨ p3) ∨ p4)) → ((p3 ∧ p5) ∨ (((True ∧ (p4 → (p3 ∨ p2))) ∨ ((p4 ∨ False) ∧ (False ∧ (p4 ∨ False)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208577972379707095169844303772 : (((False → True) → (p4 ∧ (p2 ∨ False))) → (True → (p2 ∨ (p2 → ((p1 ∧ p3) ∨ (((p1 ∧ p5) ∧ (True ∧ (p2 → (p4 ∨ p2)))) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89103292713532682296061850545 : ((((True → p2) ∨ p2) ∧ (p3 → (False ∨ (True ∨ ((p3 ∨ p4) ∨ ((p5 ∨ (False ∧ p5)) ∧ (p4 ∨ ((p4 → (p4 ∨ p3)) → p5)))))))) → p2) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187577841626381458892596579560 : ((p3 ∨ (((True ∧ (True ∧ p2)) → p5) → ((p1 → p4) → p5))) → (((p4 → p3) → ((p5 ∧ p3) → p5)) ∨ ((p2 → p4) ∧ (p1 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116336771482257577577655035937 : ((((p2 → p5) ∧ p2) → ((p5 → p3) ∧ (((p3 ∨ (((p2 ∨ True) ∨ p5) ∧ (p3 ∨ False))) ∧ p1) → ((p5 ∧ p3) ∧ p3)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299346923685331584260670246635 : (False ∨ (((False ∨ (False ∧ False)) ∨ (((p2 ∨ p2) → (False ∨ ((True ∨ p1) ∧ ((p3 ∨ p4) → True)))) ∨ ((p1 ∨ (p4 ∨ p5)) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198687679277220441769816838101 : ((p4 ∨ (True ∧ (True ∧ (p3 ∨ (p3 ∧ p1))))) ∨ ((p3 ∨ (True ∨ ((p5 ∧ (True → (p1 ∧ p4))) ∨ (False → (p3 ∨ p1))))) ∨ (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719269948540953562557806728244 : ((((p4 ∧ ((p1 → p1) ∨ p2)) ∨ (((((p4 ∧ False) ∧ p1) ∧ (p2 ∧ ((p4 ∨ (((True ∧ p3) ∧ p4) ∨ p3)) ∧ p3))) ∧ p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114571954566393653879356161096 : ((((((p4 ∧ True) ∨ (p3 ∨ ((p1 → p2) → p5))) ∨ p4) ∧ ((p5 ∨ False) ∨ False)) ∧ (True ∧ ((True ∨ (p5 → True)) → p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689285304021324155787728424926 : ((((((p5 → (p4 ∧ (((p3 ∧ (p5 ∨ p3)) ∨ p4) ∧ p4))) ∨ p3) ∧ (p3 ∨ p3)) ∨ ((p1 → ((p2 ∧ True) → (True → True))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114387177003777817675524816299 : (((((True ∨ (p2 → p3)) → (((((p3 ∨ p4) ∨ p4) → False) ∧ p3) ∧ p5)) ∨ (False ∧ False)) ∨ (p4 → ((p3 ∧ False) ∧ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47040697114614446757901687900 : ((((((p2 → ((p2 ∨ ((False ∧ p2) → p4)) → p2)) → (p4 ∧ p2)) ∨ (p3 ∧ ((p5 → True) ∧ p2))) ∧ (p4 → p1)) ∨ (False → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261219776212420856807657872172 : ((p4 → p5) → ((True → (((p3 → p5) ∧ p2) ∨ p4)) ∨ (((((p2 ∧ True) ∨ (p1 ∧ True)) → (False → (p3 → (p5 ∨ False)))) ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327120867045642507287926916300 : (True → (((p2 ∨ p1) → (p1 → ((((((p4 → (p5 ∧ p4)) ∨ p1) ∨ ((p4 → False) ∧ (p5 ∧ (p1 → False)))) → p3) ∧ p2) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



