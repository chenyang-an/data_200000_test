variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60221701188995926005042695785 : (((True → p2) → (((p5 → True) → (((p4 → (p3 ∨ False)) ∧ (True ∧ (True ∧ p1))) → (p4 ∧ (p2 → (p1 → (True → p2)))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305921069970685976210892572021 : (p1 ∨ ((True ∧ (p4 ∧ ((p1 → p2) ∧ p5))) → (p3 ∨ ((p5 ∧ p1) ∨ ((((((True ∧ p1) ∨ p5) → p2) ∧ p1) ∧ (p4 ∨ False)) ∨ True))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158600173141267533116833968211 : ((False ∧ ((((((True ∨ True) → True) → p2) → False) → (p5 → ((p5 ∨ p2) → (p3 ∧ p1)))) → p3)) ∨ (False → (True ∧ (False → (p5 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724769950370371484177621672503 : ((((p3 ∨ (False → p2)) ∧ (p3 ∨ (((p4 ∧ (False ∧ ((p3 ∨ (False ∨ p3)) ∨ ((p2 → p1) → p5)))) ∨ p3) ∨ ((p5 → p3) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147785503712313958031687428857 : ((((p5 ∨ p5) → (((((p2 ∧ False) ∧ p5) → p5) → (p5 ∧ ((False → p4) → (False → p4)))) → p1)) → p2) ∨ ((True ∨ (p5 ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175456069919724908076565248124 : ((p1 → (p4 → (((True ∧ p2) ∧ ((((p4 → p2) → False) → p5) → p5)) → p4))) → ((p5 ∨ p5) ∨ (((p5 ∨ p1) ∧ (p3 ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712717176709166199853523923717 : (((((True ∧ False) ∨ (p4 ∨ (p5 ∧ False))) ∨ (True → ((p1 ∨ p2) → ((p1 ∧ ((True ∨ ((p5 ∨ p5) ∧ p4)) ∨ (p4 ∧ p2))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186601570723378162124045745077 : ((((p5 → ((True → p2) ∨ (p1 ∨ p3))) → p4) → (p5 ∧ p3)) → (((p4 ∧ (False → (p4 → ((p3 ∧ p3) → False)))) → (True ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 → ((True → p2) ∨ (p1 ∨ p3))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166262279379164122267183423360 : ((p3 ∧ ((True → (p3 → p3)) ∧ ((p5 ∨ p1) ∨ ((False ∧ (p2 ∨ True)) ∨ (p5 ∧ p5))))) ∨ (p4 → ((((p1 ∨ p4) → p3) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610054174719789414629417858392 : (((((((p3 ∨ ((p1 ∧ (p3 ∨ (((p1 ∧ p4) ∨ p3) → False))) → False)) ∧ ((False → ((False ∨ p1) → False)) ∨ p2)) ∧ p2) → False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158142207751236707437123026923 : ((((p4 ∧ p1) ∨ (p1 ∧ p4)) ∨ ((p4 ∧ p1) ∨ (((False → ((p2 ∧ p2) ∧ p2)) → True) ∧ p5))) ∨ ((p5 ∧ (True ∧ (p2 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42086870576738385924625992835 : ((((p4 → False) ∨ (((((p4 → (p3 ∨ p4)) ∧ (p4 ∨ (((p1 ∨ p4) ∨ False) ∨ ((p4 → p1) → p1)))) ∨ p5) → False) ∧ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111324255726773802015653656505 : (((p2 ∧ (((p3 → ((((True ∧ ((p4 ∧ False) ∧ p1)) → True) ∧ (p1 ∨ (p1 → p5))) → (True ∧ p1))) ∨ p5) ∧ True)) ∧ p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173905265442404642906768807302 : (((((((p4 → (True ∨ p2)) → False) → p4) ∧ ((True ∧ p2) ∨ p5)) → p4) → p2) → (((p2 ∧ True) → (p4 ∨ p3)) ∨ ((p1 ∧ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197251892370752381822760325400 : ((((p3 ∧ (p2 ∧ (p1 ∧ p4))) → p1) → p2) ∨ ((p2 → p5) ∨ (((p2 → (True ∧ p1)) ∨ (((p3 → (True ∧ p3)) ∨ True) → p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133986964768446098686896454982 : (((((((p1 → (p5 ∧ p4)) ∧ ((p1 → ((True ∧ p1) ∧ p3)) ∨ p2)) → (p2 ∨ p5)) ∨ (False ∨ p2)) ∧ p1) ∨ p4) ∨ (False → (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258420578187165460912573425831 : ((p5 ∨ p1) → (((((p1 ∨ p3) ∧ p4) ∨ ((p2 ∨ p1) ∨ p2)) ∧ (False ∧ (p3 ∧ True))) ∨ ((p3 → p5) ∨ ((False ∧ p1) ∨ (p2 → True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50599291103594271180967678791 : ((((((((p5 → p3) → (p3 ∨ (p4 ∨ (False → (p4 → p5))))) ∨ p4) → p2) ∨ p1) ∨ (True ∨ p2)) → (False ∧ ((p1 ∨ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111108007471477417937256807057 : (((((((p1 ∧ (p5 ∨ p2)) → p3) ∨ p3) ∧ (True ∧ p2)) ∨ (p5 ∨ ((p3 ∨ (False ∧ ((False ∨ p5) ∧ False))) → p2))) ∧ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217821523056092442789194279767 : (((p3 ∨ (True ∨ True)) → p1) → (((True ∨ ((((p4 ∧ ((p5 → True) ∨ False)) ∨ (True ∨ p3)) → True) ∧ p2)) ∧ p4) ∨ ((p1 → p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190164164889646022845099521682 : (((False ∧ (p3 → (((p4 ∧ p4) ∧ p1) ∨ p1))) ∧ p1) ∨ ((((p5 ∧ (True → p2)) → ((p3 ∧ False) → p4)) ∨ (p4 ∨ p1)) ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134631504261887734744018454780 : (((((((False ∧ (False ∧ (p3 ∧ p5))) → ((p5 ∨ p4) ∧ True)) ∨ p5) ∨ p2) ∨ ((p3 ∨ False) ∧ (p5 ∧ True))) → p3) ∨ (True ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193027059084506755185811696437 : ((((p4 ∧ p2) → (p4 ∧ (p2 ∨ p2))) → (True → p3)) → (((p4 ∧ (((p1 ∧ False) ∨ p2) ∨ (p5 ∧ (False ∧ False)))) ∨ True) ∨ (p1 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47341689120627163938548978637 : ((((p3 ∨ p4) ∧ (((p4 ∨ (p4 → ((((False ∧ p1) ∧ False) ∧ (((p2 → False) → p4) ∨ p2)) ∨ False))) ∧ p2) ∧ p4)) ∨ (False ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41412722971717210944411545381 : (((((p5 ∨ ((p1 → False) → (p1 ∧ p5))) ∨ (p5 → (p1 → (p3 ∧ p1)))) ∨ ((p4 → ((p2 ∨ True) ∨ (p3 → p1))) ∨ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262139744330568914375420102724 : (True ∧ ((((p5 → ((p1 ∧ (((p1 ∧ (p3 → p5)) → (p2 ∧ (True ∧ p1))) ∧ p1)) ∨ (((False ∧ p5) → False) ∧ p2))) ∧ p4) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111423306847032243644708749509 : (((p4 ∨ (((((p4 ∨ p1) ∧ (False → p4)) ∧ ((p3 → p4) → (p2 → (p3 ∨ ((False → p5) ∨ p2))))) ∧ False) ∧ p4)) ∧ p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135471636595936843462604390792 : (((((((((p4 ∧ True) ∨ p1) ∧ p1) → p2) ∧ False) → (p1 → True)) → (p3 ∧ (p1 ∧ p4))) → ((p1 ∨ p5) ∧ p4)) ∨ ((p4 ∨ p5) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p4 ∧ True) ∨ p1) ∧ p1) → p2) ∧ False) → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((((((p4 ∧ True) ∨ p1) ∧ p1) → p2) ∧ False) → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h8
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301120143825208237656003093239 : (False ∨ (((False → p2) ∧ (((p3 → True) ∨ False) ∧ True)) ∧ (((p4 → p3) → p3) ∨ (False ∨ ((p1 → False) ∨ ((p5 ∧ (False ∧ p3)) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227077970012867584527704433765 : (((p3 ∨ p2) → p4) ∨ ((((p5 ∨ (p2 ∨ ((p3 ∨ p5) → (False ∨ ((True ∧ p1) ∨ p3))))) → ((p3 ∧ p5) ∨ p2)) → p4) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41284305281866254080252967740 : (((((p4 ∧ ((False → ((True → (p2 ∨ (True → p3))) → p1)) ∧ (p1 ∧ p1))) → (p5 ∧ p5)) → (False ∧ (p2 ∧ (p2 → False)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102563847701408203961867959398 : (((p3 → (((p4 ∧ p2) ∨ ((((True ∧ p4) ∨ (p1 ∨ (p4 ∧ p5))) → False) ∧ (p3 ∧ ((False ∧ p5) ∧ p1)))) ∨ True)) ∧ True) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249605021453989874317712891611 : ((p5 ∨ p3) ∨ ((((((p2 → (True ∨ p3)) → p1) ∨ (False ∧ (p3 → ((p5 → p3) ∧ ((p2 → p4) → False))))) ∧ p2) ∨ True) ∨ (p1 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117896775203329282110893010656 : ((p5 ∧ ((((False ∧ (p4 ∨ (((True ∧ p4) → p2) ∧ p3))) ∧ p4) ∧ ((p2 ∧ p5) ∧ (p3 ∧ False))) ∨ (False ∨ (p2 ∨ False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46257119865841593580901017520 : (((((((p3 → (p3 ∧ ((p1 → True) → p3))) → p2) ∧ ((p5 → p4) ∨ True)) → ((p3 → p2) → p5)) → (p2 ∨ False)) ∧ (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648537142500202870731475503719 : ((((((p4 → ((True ∨ p2) → (((p1 ∧ p3) ∧ False) → (((True → True) ∧ p3) ∨ p3)))) → (p5 → (p4 ∨ p4))) ∨ True) ∧ (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47805540136633223790513885625 : (((((((p1 ∧ p2) ∨ (p1 ∨ ((True ∧ False) → p5))) ∧ (((p2 → p5) → False) ∧ (False ∨ p2))) ∨ (True ∨ True)) → p4) → (True → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∧ p2) ∨ (p1 ∨ ((True ∧ False) → p5))) ∧ (((p2 → p5) → False) ∧ (False ∨ p2))) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59157744256310428073159130089 : (((False ∨ p1) ∨ (p2 ∨ ((p2 ∨ (p2 ∨ ((p2 ∨ (((((True → p4) → (False ∨ True)) → p5) ∨ p5) ∧ True)) → (p4 ∧ False)))) ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_150449168346308406877321528296 : (((((((p1 ∧ p2) ∧ p3) → (((True ∨ p5) ∧ p4) ∧ p3)) → ((False → False) ∧ (True ∨ False))) → p5) ∧ p3) → (p4 ∨ ((p4 ∨ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342474199869056375329421423389 : (p2 → ((((((p4 ∧ (p3 ∨ p2)) ∨ p2) ∧ ((p3 → p1) → p3)) ∧ p5) ∨ p2) ∨ (p5 → ((False ∧ (p3 ∧ (p3 ∨ True))) ∧ (p5 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700074362789095677722179867453 : (((((p2 ∧ (p1 → True)) ∨ (((p1 ∨ p2) ∧ (p1 ∨ p3)) ∧ p2)) → ((((p4 ∧ p4) ∨ (p5 ∧ (p4 ∨ False))) → (p1 ∧ p4)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117806043420307741116411648139 : ((p4 ∧ (((p4 ∨ p5) ∧ p4) ∨ (True → (((p2 ∧ (p4 ∨ (False ∨ (False ∧ p5)))) ∨ p4) ∨ (p5 ∨ ((p2 ∨ False) → p1)))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148934956479256328306099075737 : (((p1 ∧ (False ∨ (p3 ∨ True))) → (True ∧ (p3 ∨ (((p4 → (((p3 → False) ∨ p5) ∨ p2)) ∧ p5) ∧ True)))) ∨ (p2 → (False → (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736852418928675738435971338415 : ((((p2 → p4) ∧ ((False ∨ ((((((((p3 ∨ True) ∨ (True ∧ p4)) ∧ (True ∧ p2)) ∧ p1) ∨ (p5 ∧ p2)) → p5) → p2) → p2)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177643806067549668996619599784 : ((((False → (((p2 ∧ False) ∨ (p3 → p3)) ∨ (p1 ∧ True))) ∧ p4) ∧ True) ∨ ((p1 ∨ p1) → ((p5 ∨ ((p5 ∧ p3) ∨ True)) ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798329872778679797210914137816 : (((p1 → (((p1 → p2) ∧ (p1 → (p2 → (((p5 → p3) → (p4 → False)) ∧ p1)))) ∨ ((p4 → (((False ∧ p5) ∨ p1) ∧ p1)) ∨ True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_89032331213493898599666814228 : ((((p1 → False) ∧ p1) ∧ (((((True ∧ (False → p1)) ∨ p2) ∧ p3) ∨ p2) ∧ (False → (True ∨ (p2 → (((p4 → True) → True) ∧ p5)))))) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782644718716281932126989994859 : (((p3 ∨ (((((p5 ∨ ((p1 → p5) ∧ (p4 ∨ (p5 ∧ (p5 ∨ p1))))) ∧ (p4 ∧ True)) → ((p3 ∨ (False ∧ p1)) ∧ p1)) ∨ False) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304683646142386674194367863647 : (p1 ∨ ((((((p2 ∨ p1) ∧ (((p4 ∧ ((True → p4) ∨ (((p1 ∨ p2) ∧ p1) → p3))) → p4) ∨ True)) ∨ p2) ∧ p5) ∨ True) ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351744413390479373116587201180 : (p4 → ((True → (((p1 → p5) ∨ True) → (((p5 ∨ (p5 ∧ p1)) ∧ True) ∧ p2))) ∨ ((((p5 ∨ p5) → p5) ∧ p4) → ((False → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45868683310882345629729234151 : (((p3 → (((((((p3 → True) ∧ False) ∨ p1) ∧ p5) ∨ (p5 → False)) ∨ (True ∨ (((p4 ∨ p1) → False) → p5))) → (p1 ∧ p2))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800626051947070709600042078227 : (((p2 → (((True → (p2 ∧ (p3 ∨ True))) → (((p1 ∨ True) ∨ p4) ∧ ((((False ∨ False) ∨ p1) ∨ True) ∨ ((p1 ∨ p2) ∧ p3)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356320516803247357987311531495 : (p5 → ((((p5 ∨ (((p2 ∧ p1) ∨ p2) ∨ p5)) → (p4 → False)) ∨ (True → p5)) ∧ (((p3 → (p2 → p1)) → (p5 ∧ (p4 ∧ True))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136375323937107615580513265614 : ((((True ∨ (False → p4)) → False) ∨ ((((((p1 → p5) ∨ p5) ∨ ((p3 ∨ False) ∨ (True ∨ p2))) ∨ False) ∧ p1) ∨ p1)) ∨ ((p4 ∧ p1) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52060259197374882943881491298 : (((p5 → ((p3 → (True ∧ (p5 ∨ ((False ∨ p3) ∨ p1)))) ∧ (False ∨ (False ∨ p1)))) ∨ ((True ∧ (p4 ∨ (p4 ∨ (p3 → True)))) ∨ p1)) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621774458988540427861050810351 : ((((p1 ∧ ((((p5 ∨ ((((p5 ∧ p3) → p4) ∨ p3) ∨ p3)) ∧ True) → (((False → (False ∨ p5)) ∨ p1) ∨ (p2 ∨ True))) → False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336662962902046670755835280792 : (p1 → (((((p2 ∧ p4) ∨ (True → p5)) → (((p2 ∧ (False → (True ∧ False))) ∧ (p5 ∧ p2)) ∨ False)) ∧ ((True → (p2 → False)) ∧ p5)) → p4)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 ∧ p4) ∨ (True → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h7
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797844115983539895999291793146 : (((p1 → ((((p2 ∨ p2) ∨ (p2 ∧ (((((p2 → (True → p5)) ∨ False) ∨ p5) ∨ (p4 ∧ (True ∨ p3))) ∨ p5))) ∧ p3) ∨ (True ∧ p1))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14364742819078293614218228766 : (((True → (((p3 → ((p1 ∨ ((p2 → (p4 ∨ p5)) ∧ (((p1 ∧ p1) ∨ p1) ∧ True))) ∧ p5)) ∧ p1) ∨ (p5 ∨ True))) ∧ (p1 → True)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183949437763990850327547696179 : (((p4 ∨ (((p3 ∨ p5) ∧ ((p4 → True) → p1)) ∧ p2)) ∧ False) ∨ (p3 → ((p4 ∨ ((p4 ∨ p2) → p5)) ∨ (p1 ∨ ((p5 ∧ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347027902292683433157104538449 : (p3 → ((p4 ∨ (p2 ∧ ((p3 ∨ False) ∧ (p2 → ((p1 ∨ True) → ((False ∧ p4) ∨ p1)))))) ∨ (False ∨ ((True ∧ (True ∧ False)) → (p2 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664653734384909926821558034935 : ((((True → (p2 ∧ (p1 → ((p1 → ((((p1 ∨ (((p1 → p1) → (p4 ∧ p3)) ∨ True)) ∧ True) ∧ p2) ∨ p4)) ∧ True)))) → (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341075930319141919528720231439 : (p2 → ((True → (((p3 → (p5 ∨ (p5 → (((p2 → p5) → False) ∨ False)))) ∨ ((p3 ∨ (p1 ∨ p4)) ∧ (p4 ∨ p5))) ∧ (True → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160175953286893456447865294201 : ((((p2 ∨ p5) → (((p3 → ((p2 ∧ p2) ∧ p1)) → False) → (p4 ∧ (p3 ∨ p2)))) ∧ (p3 → p5)) → (p4 → ((p4 ∧ p1) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758417165321083261331950717819 : (((p2 ∧ (((p2 ∧ (True ∧ p2)) ∧ ((((((p5 ∨ ((p5 ∨ (p5 → p2)) ∧ False)) → True) ∧ p5) ∧ p4) ∨ True) ∨ (p4 ∨ p5))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113512729560335106310439329106 : ((((((((p5 → (p4 ∧ False)) ∧ p2) → p4) ∨ (p5 → p5)) → False) ∨ ((((True ∨ p3) → False) ∧ False) ∧ p1)) ∨ (p3 ∨ True)) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37712765666891693703611314938 : ((((((((((p1 ∨ p1) → p1) → p5) → p5) ∨ False) ∨ (p5 ∧ ((p3 → p1) ∨ True))) ∨ (p4 → ((True → p3) ∨ p3))) → p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219485787373334301398544907871 : ((p5 ∨ ((True ∨ True) ∧ p5)) → ((p3 ∨ p2) ∨ (((p4 ∨ p5) ∨ (False → (((p2 ∨ True) ∧ (False ∨ p3)) ∧ ((p3 ∨ p1) ∨ p5)))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80464044502879007612961306514 : (((((p5 ∧ (p2 → p2)) ∨ p3) ∨ (p4 ∨ (p2 ∨ (((((p2 ∨ p1) → p4) → p1) ∧ ((p1 → True) ∨ p5)) → True)))) → (p4 ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (p2 → p2)) ∨ p3) ∨ (p4 ∨ (p2 ∨ (((((p2 ∨ p1) → p4) → p1) ∧ ((p1 → True) ∨ p5)) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164472342836099096091926195844 : (((((p4 ∧ (False ∨ (False ∨ ((True ∨ p2) ∧ p4)))) ∨ (p3 → (False → p4))) ∨ False) ∧ False) ∨ (True ∨ ((p3 ∨ ((p4 ∨ False) ∨ p2)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669971874715078120784368542178 : ((((((p2 → ((((p4 ∧ p5) → p5) ∨ p4) ∧ p1)) ∨ p3) → ((p4 ∧ (p1 ∧ False)) ∨ ((p1 → p3) ∨ True))) ∨ (p5 → (True ∨ p2))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167768758198917742023778637234 : ((((p1 ∧ ((p1 ∨ (((p3 ∧ p4) ∨ True) ∨ p5)) ∨ p1)) → p1) → (p4 ∧ (p5 ∧ p5))) → (((False ∧ p1) → p1) ∧ (p5 ∨ (p5 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∧ ((p1 ∨ (((p3 ∧ p4) ∨ True) ∨ p5)) ∨ p1)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h16 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h5
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357007618737751628913345845796 : (p5 → (((p4 ∧ p1) ∨ p2) ∨ (((p3 ∧ p4) ∨ (False → p3)) ∨ (((p2 ∨ ((p4 ∧ False) → (p2 → ((False → True) ∨ p2)))) ∨ p5) ∧ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708342299686991033237334029722 : (((((((False ∨ p2) ∧ (False ∧ False)) → False) ∧ p5) → (p3 → (p1 ∧ (((p3 ∧ ((p5 ∧ True) ∨ p4)) ∨ (p4 → p5)) → (p2 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184583772337545743823420106690 : (((True ∨ (((p3 ∨ p3) → (p1 ∨ False)) ∨ p1)) → (p2 → p1)) ∨ ((((p1 ∧ True) → True) ∨ p5) → (((True → p4) ∧ (p1 ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_343018200701946342713683512871 : (p2 → ((((p2 ∧ p2) ∧ p5) ∨ p5) → (p3 ∨ ((True → (((True ∨ True) ∧ False) ∨ (p1 ∨ (False ∨ ((p5 ∧ True) → (p2 ∧ True)))))) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45485542397385957427836389142 : (((False ∨ (((p3 ∧ p3) ∧ True) ∨ (p4 ∧ (True ∨ (((p4 ∨ ((p3 ∧ p2) → (p5 ∨ (False → (False → False))))) ∨ p1) ∧ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164804502266585461231191974557 : (((((False → p2) ∧ p3) → (p5 ∨ ((p5 ∧ (True ∧ (p5 ∧ (p1 ∧ p4)))) ∨ False))) ∨ p4) ∨ (p3 → ((p4 ∨ ((p2 ∧ p2) ∧ False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355871179296763241947905699195 : (p5 → (((p1 ∨ p1) ∧ (True → ((((p2 → False) → p4) ∧ (False → p4)) ∧ (p2 ∨ (p2 ∧ ((p2 → p2) ∨ p4)))))) ∨ ((False ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251222449217612144230536569351 : ((p2 → p1) ∨ (p1 → (((((p4 ∧ (p5 ∧ (p4 → p4))) → p5) → ((p4 ∧ (p1 ∧ p1)) ∧ False)) ∧ p1) → (((p1 → p2) ∧ p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∧ (p5 ∧ (p4 → p4))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h5
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763700042398070109160775067065 : (((p3 ∧ (False ∨ (((p3 → (p1 → True)) ∧ ((p3 → (p3 → ((((False ∨ p2) ∨ p4) ∨ p4) ∨ (p4 ∧ p3)))) ∨ (p3 → True))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317934922024506599196949333278 : (p4 ∨ ((p1 ∨ ((p4 ∨ p2) → ((p1 → (p1 → ((p4 ∨ (p1 ∧ ((False ∨ True) ∨ p2))) ∧ (p5 → (p5 ∧ (p3 ∨ p1)))))) ∨ p3))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118726895760818836423472965717 : ((p5 ∨ (((p2 ∨ ((p4 → p5) ∧ p5)) → (((True → True) ∨ ((p1 → False) ∧ p1)) → p1)) ∧ (True ∨ ((p4 ∨ p4) ∧ True)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164585518271916503774985125881 : ((((True → p2) ∧ ((p5 ∨ p3) ∨ (((p3 → (p5 → p2)) ∨ True) → (p2 → p4)))) ∧ False) ∨ (((p4 ∨ p4) ∧ ((p4 → True) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148585239843467286237876844024 : ((((((p5 ∨ p4) ∧ p3) ∧ (p1 ∧ False)) ∧ (True → p4)) ∨ ((((True ∧ (p1 → True)) ∨ p5) ∨ False) ∨ True)) ∨ ((p4 → False) → (False → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319747643962094038697982701244 : (p4 ∨ (((p5 ∧ p5) ∧ (p1 → (True ∨ p5))) ∨ (p4 ∨ (p3 → ((((p5 ∧ p3) ∨ p1) ∨ ((p2 ∨ p3) ∧ False)) ∨ ((False → False) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187116307799850612675152100832 : (((p4 ∧ False) ∨ ((False ∨ p2) → ((p5 ∧ (p3 ∧ True)) → True))) → ((True → p1) ∨ (p1 → (((False ∨ (True ∧ p4)) → p4) ∧ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130185662240153894217428379359 : (((p4 ∨ (((False ∧ p2) ∧ (False ∨ p3)) ∨ ((p2 → True) ∨ (((p1 → p3) ∨ (p3 ∨ p4)) → p1)))) ∨ (p2 → p3)) ∧ (True ∨ (False ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_907379910797586017015772875005 : ((((((p5 ∧ p1) ∨ p1) → (((p3 ∧ True) → (True ∧ ((((p5 ∨ p2) → p2) ∨ False) → p5))) ∨ p1)) → (False ∧ (p4 ∧ (p4 → p3)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p1) ∨ p1) → (((p3 ∧ True) → (True ∧ ((((p5 ∨ p2) → p2) ∨ False) → p5))) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117505994749003109606675785508 : ((p2 ∧ ((p2 ∧ ((False → (p2 ∨ ((p4 ∨ (p3 → p3)) → (p3 ∨ p2)))) → (((p3 → p5) → (p4 → True)) ∧ p4))) ∧ p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225615944955758973007079244709 : (((p1 → p1) ∧ p4) ∨ ((((p2 ∨ p2) ∧ (False ∨ p5)) ∨ (((p5 → ((False → False) ∨ (p1 ∧ p1))) ∨ p3) ∨ (p4 ∧ False))) ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744517812127452857499023114208 : ((((p2 ∧ p2) → (True → (((p1 ∨ (p2 ∨ True)) → (((p3 → p1) ∨ (p2 → False)) → (p2 ∧ False))) ∨ ((p4 ∧ False) → (p1 ∧ True))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166737871951985952130757552913 : ((p4 → (((p3 ∨ (((p1 ∧ True) ∨ ((p5 ∨ False) ∧ True)) ∨ True)) ∨ (False → True)) → p3)) ∨ (((True ∧ p5) → True) ∨ (p1 ∧ (False ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171881308210393360375616602914 : (((True ∨ (((((p3 ∨ (p4 ∧ p1)) ∨ False) ∨ True) → p4) ∧ (p2 → True))) → p5) ∨ (p4 → (((p1 ∨ ((True ∧ p4) ∧ False)) → True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317098393576535955135829472133 : (p3 ∨ (p5 → ((p1 → (p1 ∧ ((p4 → ((p2 ∨ (p2 ∨ False)) ∧ (p1 ∧ False))) → ((((p3 → (p4 ∨ p2)) ∧ p4) ∨ p1) ∧ True)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309394047292352459342068353484 : (p2 ∨ ((False ∨ (((True → False) ∨ (p3 → True)) → (p2 ∧ ((((p4 → True) ∧ p1) ∨ True) ∧ (False → (p1 ∧ (p3 → p1))))))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740341060850122065182476233676 : ((((p1 ∨ p1) ∨ (p5 ∧ (((True → ((p2 ∧ (p5 → p3)) → p4)) ∨ (p4 → ((False ∧ ((p3 ∨ (p2 → p3)) → p4)) ∨ True))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301788704023372018243071408757 : (False ∨ ((p2 ∧ p4) ∨ (((p2 ∧ (True ∨ p5)) ∧ ((p3 ∧ (p3 ∧ (((p3 ∨ p3) → (p3 ∧ p1)) ∧ p5))) ∨ (p3 ∨ True))) ∨ (False → True)))) := by
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
theorem thm_5_vars_324856624482406609940095289638 : (p5 ∨ ((p1 → p1) ∧ ((((p1 → (p4 ∨ (True ∧ p5))) ∧ False) ∧ ((p3 ∨ (p4 → (p1 ∨ p1))) ∨ p3)) ∨ (((False → p4) ∨ False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150707993203820210812554887673 : (((((p4 ∧ (p1 ∧ ((False ∨ ((p5 ∧ (p1 ∨ False)) → p2)) → (p3 ∧ (p3 → p4))))) → p2) ∧ p5) ∨ p1) → ((p1 ∧ p3) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



