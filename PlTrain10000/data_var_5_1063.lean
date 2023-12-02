variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650845110977436441880955992984 : ((((((p4 ∨ (((p5 ∧ p2) ∨ False) → p4)) → p2) → ((((p4 ∨ p2) ∧ p1) ∧ p5) ∧ ((p4 ∧ p4) ∨ (p1 ∧ p4)))) ∧ (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157291932016663523956547728181 : ((((p2 → p1) ∨ ((p3 ∨ (p1 ∧ p2)) ∧ (True → ((True ∧ False) ∨ (p5 ∨ (p5 → p1)))))) → p3) ∨ (p2 → (True ∨ ((p4 → p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354773025756359441555770634622 : (p5 → (((p1 → ((((p3 → True) ∨ False) → p1) ∨ (p1 ∨ p4))) ∧ ((True → True) ∧ (p3 ∨ ((p2 ∧ (p2 ∨ p4)) ∧ (p1 ∧ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1957598267239166204964345923 : ((((((p4 ∧ p4) ∨ False) ∧ (p1 ∨ p2)) ∨ (p1 ∧ p4)) ∧ (p5 → (((False → p1) → p3) ∨ p3))) ∨ (((p5 ∧ p3) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218584876232958199834632422620 : (((p2 → p3) → (p2 ∧ p4)) → (((((p3 → (p5 → p3)) ∨ p2) → p1) ∨ p1) ∨ (False → ((p2 ∨ ((p1 → (p3 ∨ p5)) → p4)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354887378649593146157771798575 : (p5 → ((p3 ∧ ((((((p2 ∧ ((False ∧ p4) → (p1 ∨ p2))) → p2) ∨ p2) ∧ (p3 → ((p2 ∧ p5) ∧ p2))) → (True → p3)) ∧ p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118162418960598802112734206152 : ((False ∨ (((False → p5) ∨ p5) → ((p5 ∧ (p4 ∨ (p3 ∧ p2))) → ((((False → False) ∨ ((True ∧ p4) ∧ p5)) ∨ p1) → p3)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259127904439997212490279109515 : ((False → True) → ((((((False ∧ False) ∨ ((True → (False → p1)) ∨ True)) → p5) ∧ (p1 → ((p3 → False) → ((False → p3) ∧ True)))) → p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∧ False) ∨ ((True → (False → p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785968515377681424229659348151 : (((p4 ∨ (((p3 ∧ ((((p1 ∨ (((p2 → p3) → p1) ∧ p2)) ∨ True) → p4) ∧ p5)) ∧ ((p2 ∨ p3) → (p1 → True))) ∨ (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_851761799516746708368666467832 : ((((True → (p3 ∧ (True ∧ ((((((p1 ∧ (p4 ∧ (p3 ∨ p1))) ∨ p3) ∧ p5) ∧ ((p5 ∧ p5) → p1)) ∧ (p2 → True)) ∧ p4)))) ∨ p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179036375952174400062872914535 : (((p5 ∨ p4) → (((p4 ∧ p1) ∨ p5) ∧ (p5 ∨ (p2 ∧ (p1 ∧ p4))))) ∨ (True ∨ ((True → (p3 → ((p1 ∨ False) ∨ p2))) ∧ (False ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589556302739666476847547779949 : ((((((((True ∨ (p5 → False)) → (p4 ∧ ((True → (((p4 ∧ True) → p5) → True)) → (p5 ∨ False)))) ∧ (True ∧ p4)) → p3) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192640524629457688589193172511 : (((((p4 ∧ p1) ∧ (p5 → (p2 ∧ p3))) ∨ True) → p5) → (p3 → ((p2 ∧ p2) ∨ ((p4 ∨ (True → (p4 → (p1 ∨ (p1 → p5))))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ p1) ∧ (p5 → (p2 ∧ p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141330810398429003420398717709 : (((((True → p2) ∧ p4) → p5) ∨ ((p4 ∧ True) → (p2 → ((((p4 → (True ∧ False)) ∨ (False ∧ p3)) ∨ p1) ∧ p4)))) → (p2 ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204163156667861958721844638764 : (((((p1 ∨ p5) → p5) ∨ False) ∧ p2) ∨ ((p1 ∨ ((False ∨ p2) ∨ (p5 → ((p5 ∨ (False → (p1 ∨ p2))) → p4)))) ∨ (p4 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_689587045129200631284250680924 : (((((p5 ∧ (((False → p1) ∧ True) ∧ p2)) ∧ (p4 ∨ ((p1 → p2) ∨ (True ∧ p4)))) ∨ (p2 ∧ ((p4 → (True ∨ p2)) ∧ (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616288999444797053877922915761 : (((((((False ∧ p5) ∧ (((p2 ∧ p1) ∨ p1) ∧ False)) ∨ (False → True)) ∨ ((p4 ∧ (((True ∨ (p3 → p1)) ∨ True) ∧ False)) ∨ p2)) ∨ p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_322850087848377600553409657330 : (p5 ∨ ((((((True ∧ (False ∧ p3)) ∧ p4) ∧ False) → p2) → ((p2 ∨ p3) ∧ ((False ∧ (p5 ∨ True)) ∧ ((p1 → (False ∨ True)) ∨ p2)))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∧ (False ∧ p3)) ∧ p4) ∧ False) → p2) := by
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
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139620801338377900891442704155 : (((((False ∨ (p5 ∧ False)) ∨ ((p2 ∨ p3) ∨ (p2 → p4))) ∨ (((((p2 ∨ True) → True) ∨ p2) ∧ p5) ∧ True)) → p2) → (p4 ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223750969564464372776935894635 : ((p2 ∨ (True → True)) ∧ ((False → p1) ∧ (p5 ∨ ((p5 ∧ (p4 ∧ (p1 ∧ ((p5 ∨ (p3 ∨ (p3 → (p4 ∧ p5)))) → p5)))) ∨ (p5 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185593214728932553940074694020 : ((p5 ∨ ((p5 ∧ p5) ∧ ((((True ∨ p1) ∨ p4) ∧ p3) ∧ p2))) ∨ (True ∨ (p1 ∧ (p4 ∧ ((False → p4) ∨ (((p4 ∧ p1) ∧ p3) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40980855217600035277711038388 : ((((True ∧ ((p2 ∨ (p4 ∨ ((False ∨ p2) ∨ ((p1 ∨ (True → p2)) ∨ (((p1 → False) → p2) ∨ p1))))) ∧ p5)) ∨ (p3 → True)) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62155264041959307904387832801 : ((p2 ∧ (p1 → ((False ∨ (True → (p4 ∨ ((p3 ∨ p2) ∨ p5)))) ∨ ((False ∧ (p5 ∨ (True ∨ p3))) → (False ∧ ((p2 ∧ False) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208585927251726823554534212462 : (((p1 → p1) → (p1 ∧ (p4 → p1))) → ((((p4 ∨ p2) ∧ (p3 ∧ p4)) → ((True ∨ p5) → p2)) ∨ (((p2 → True) → True) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_637706923695565133562329790144 : ((((((((p3 ∨ p3) ∧ (False ∨ p4)) ∧ True) ∨ (False ∧ p2)) → ((p4 ∨ (p1 ∧ (p3 → (p1 → (False ∧ (p3 ∧ p1)))))) → p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54523550351561373413263887815 : ((((p3 → p4) ∧ (p2 ∨ (p5 ∨ (p4 → p5)))) ∨ (False ∧ ((((p2 ∧ p5) ∨ ((False ∨ p3) ∧ p3)) → (True ∨ False)) ∧ (p2 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133876398912514497956780716903 : (((p4 ∧ ((((p5 ∧ (False ∧ p1)) ∨ p1) ∧ p1) ∧ (True → ((True ∧ True) ∨ (p3 ∨ ((p2 ∨ p5) ∨ p3)))))) ∧ False) ∨ (False → (p3 ∧ p4))) := by
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
theorem thm_5_vars_244068532512201779563202466830 : ((True ∧ p3) ∨ (((((p1 ∧ (p3 ∨ (p5 → p4))) → p4) → p4) ∧ ((p4 → (p1 ∧ p1)) ∧ (p1 ∧ (False ∧ (p5 ∨ (p4 → p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702122201804126824588540963087 : ((((p3 → (p4 ∨ (((False ∨ (p5 → p1)) ∨ p4) ∧ p2))) ∧ (p2 ∧ ((p4 → (p4 ∨ p5)) ∨ ((p2 → True) ∨ (False ∨ (p1 ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157369482393165982420764984308 : (((p4 → ((p5 ∨ ((False ∨ True) → (((p4 ∧ (True ∧ False)) ∧ (p5 ∨ p3)) → p4))) ∧ p5)) → p1) ∨ ((p1 ∨ False) → (False → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53382265982786857425961857215 : ((((((p3 → p1) → p1) ∨ (((p3 ∨ False) ∨ p5) ∨ p4)) → True) → (((p1 ∨ p1) → (p4 ∧ p3)) ∨ ((True ∨ True) ∨ (p3 → False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4054092835736391637942151301 : (p2 ∨ (((p2 ∧ False) ∨ p3) ∨ (p1 ∨ ((p4 ∧ ((p2 → (p1 → (True ∧ (p4 → p5)))) → p5)) ∨ ((False ∧ False) → (p3 ∨ True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125524178062194047342094225391 : (((p5 ∨ p1) ∧ (p3 → (((p1 → p4) ∧ ((p4 ∧ p3) → (p2 → ((p5 ∨ (False ∧ (p4 ∨ (p4 → p4)))) ∧ p1)))) → p3))) → (p4 → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52617816502605905627768185996 : ((((p3 ∨ (p3 ∧ True)) ∧ ((((True ∨ (True ∨ p1)) ∧ p3) → False) → False)) ∨ (p5 ∨ (False → (((p1 ∧ p1) → False) ∧ (p5 ∨ p5))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340698038522966947138683889035 : (p2 → (((((False ∧ ((p5 ∧ p1) → p4)) → (((p4 ∨ p2) ∨ ((p5 ∨ (False ∨ ((p2 → p1) → p3))) ∨ False)) → p2)) → p1) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111832691785237554950762215398 : (((((p3 ∧ (p5 ∨ (p5 ∧ (((p3 ∨ p4) ∧ ((False ∧ (p2 ∨ p5)) ∧ p1)) ∨ p1)))) ∧ p1) ∨ (p1 ∧ (p2 ∧ p2))) ∨ p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305502053206526426478209983466 : (p1 ∨ (((True ∨ ((p3 → p4) ∨ p4)) ∧ ((p5 → ((p4 ∨ p4) ∧ p1)) ∨ p5)) ∨ ((p1 ∨ False) ∨ (p5 ∨ ((True → p5) ∨ (True ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111763011879361661851595330119 : ((((((p2 → ((p1 ∧ ((p4 ∧ (True → p2)) ∨ p4)) → p2)) ∧ p4) ∧ (p5 → (p1 → (p2 ∨ p2)))) ∧ (p5 ∨ False)) ∨ p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149369158103774339270124877964 : (((False → p5) → (p2 → ((p3 ∨ (((p2 → p5) ∨ (False ∧ (p2 → p3))) → p4)) ∨ ((p1 ∨ p4) ∧ p3)))) ∨ ((p1 ∨ (False ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159965482688970750933109645433 : ((((((p2 → ((p3 ∨ False) → (p5 ∧ True))) ∨ (p5 → True)) → p1) ∨ (p2 ∧ (p2 ∧ p4))) → False) → ((p1 → ((p3 ∨ False) ∧ p5)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p2 → ((p3 ∨ False) → (p5 ∧ True))) ∨ (p5 → True)) → p1) ∨ (p2 ∧ (p2 ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((((p2 → ((p3 ∨ False) → (p5 ∧ True))) ∨ (p5 → True)) → p1) ∨ (p2 ∧ (p2 ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57146717124114021345477436553 : ((((p4 → p3) ∧ p4) ∨ (((False ∧ ((p1 ∧ (p4 ∧ p1)) → True)) ∨ False) ∨ ((p5 ∨ ((p5 ∧ (False ∨ True)) ∨ (True ∨ False))) ∧ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237979097965537258851694695305 : ((True ∨ False) ∧ (p3 ∨ (((((p4 ∨ False) → p3) ∨ (((p5 ∧ (p2 → (p5 ∨ ((p5 → (False → p5)) → p5)))) ∧ p3) ∨ p1)) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_4605922237155937281972139324 : (p4 → ((p5 ∧ p4) → ((((True ∧ p3) → ((p3 ∧ True) → ((p1 → (False ∨ p1)) ∧ (p2 ∧ (p2 ∧ (False ∧ p3)))))) → False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309379874929591504417887854196 : (p2 ∨ (((p1 → p3) → (((((p3 ∧ p3) ∧ (p1 ∧ ((True ∨ p1) ∨ ((True ∧ (p5 ∨ p4)) → True)))) → False) ∨ True) ∧ True)) ∨ (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41304870008288832913043042679 : ((((((True → (p5 → ((p2 ∨ (p4 ∨ (p3 ∨ p1))) → p1))) ∨ (True ∧ p1)) ∧ False) ∧ (p2 → ((p5 ∧ p2) → (False → p4)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147731202101103650741347732992 : ((((((p3 ∨ (p1 → False)) → False) → p1) → (p3 → (p5 → ((p2 ∧ (True ∧ p3)) ∧ (True ∨ p3))))) → p2) ∨ (p4 → ((True ∨ p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321198165888198634021749308119 : (p4 ∨ (p3 ∨ (((p5 ∨ ((p3 ∨ p2) ∨ False)) → False) → ((p4 ∧ (p2 ∧ p2)) ∨ (((p5 ∨ (p1 ∧ ((p3 → p5) ∧ p3))) → p1) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167704141241916908693926378244 : ((((p3 ∧ p3) → ((True ∨ True) → ((p1 → p4) ∧ (False ∧ p5)))) ∧ ((p3 → p4) ∨ True)) → ((((p5 ∧ p2) → p5) → (p3 ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_41722500849100386981757815640 : (((((p3 ∨ (p4 ∨ p2)) ∨ p1) ∧ (((False ∨ p2) ∨ ((p2 ∧ (p4 → False)) ∨ ((((True ∨ p3) ∨ p5) → False) ∨ p2))) ∧ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114916139592116897724337531968 : ((((p4 ∨ (((p3 ∨ p1) → (p3 ∧ ((p3 ∧ True) ∧ p3))) → False)) ∨ p1) → ((((p2 ∧ p2) ∨ p4) ∨ (False ∨ True)) ∧ True)) ∨ (p4 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343358629654941302498052740349 : (p2 → ((p3 → True) ∧ ((p4 → (p2 ∨ p3)) → (((p1 → ((p4 ∧ p5) ∧ (True ∨ False))) ∨ (p2 ∨ p1)) ∧ ((p2 ∨ p2) ∧ (p5 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587680331390076323739512188618 : ((((((((p5 → True) ∧ p1) ∧ ((((p4 → p1) ∨ (p4 ∨ (p2 ∨ p5))) → ((False ∧ True) ∨ (p4 ∧ p1))) ∧ p4)) → p2) ∨ True) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300538308133624866192774148931 : (False ∨ (((True ∧ ((((p3 ∨ (p5 ∨ ((p2 ∨ (p3 ∧ (False ∨ p5))) ∧ True))) ∧ False) ∧ True) ∨ p1)) ∨ p3) ∨ (True ∨ ((p1 ∨ p5) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114388998432247991158133817372 : (((((p5 ∨ ((p2 ∨ ((p1 ∨ (p5 ∨ (False ∧ p4))) → False)) ∧ False)) → p5) → (p1 ∨ p4)) ∨ ((False ∨ p4) → (p4 → True))) ∨ (p4 ∧ p2)) := by
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
theorem thm_5_vars_116955330566693911009520414822 : (((p2 ∧ p5) → ((p4 → (p3 ∨ p4)) ∧ (p4 ∧ (((((False ∨ p3) ∧ p2) ∧ p4) ∨ (False ∨ (p3 ∧ False))) ∨ (p3 → False))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345189195376891821545134320143 : (p3 → (((p4 ∨ p4) → ((((p1 ∧ p2) ∧ p3) ∨ p2) ∨ ((p2 → (((p5 → ((False ∧ p1) ∧ p4)) ∨ (p5 ∧ p5)) ∧ p4)) ∨ p3))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53923859531633855752883255749 : (((p3 ∨ ((False ∧ p2) ∨ ((p4 ∧ (p1 ∨ p2)) ∨ False))) ∨ (True ∨ (False → ((p1 ∨ ((p3 → ((p2 → p5) ∨ p2)) ∧ True)) ∨ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773258754512457027790225453427 : (((False ∨ ((((p3 → p2) ∨ (p3 ∨ (p5 ∧ (((p3 → p3) ∨ p5) ∧ p4)))) ∧ ((p5 → p5) ∨ ((p1 → p1) ∨ (p2 → p3)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57969997665730308858471424296 : (((p3 → (p4 ∧ p2)) → ((True ∧ ((True → (p4 ∨ p1)) → (((True ∧ (False ∨ p1)) → ((p2 ∨ (p4 ∨ False)) ∧ False)) ∨ p1))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253640355035547392440126198318 : ((p1 ∧ True) → (p1 ∧ ((((p4 ∨ (False ∨ p5)) ∨ p1) → ((p1 ∨ (p1 → ((True ∨ p1) ∨ False))) → (False ∧ p5))) ∨ ((False ∨ p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42629447255505188352544596076 : (((p3 ∨ ((False ∨ False) ∧ (p5 ∨ (True ∧ ((((p1 → False) ∨ p3) ∨ ((p2 ∨ (p3 ∧ True)) ∧ (False ∧ p5))) ∨ (p1 → p2)))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50921552322411835836348322826 : ((((((False ∧ p1) ∨ (((p5 ∧ p4) ∨ (False ∨ False)) ∨ p1)) ∨ True) ∧ ((p1 ∨ p3) → True)) ∧ (((p4 ∧ p2) ∨ p1) → (True ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_131881909539197312965657403411 : (((p2 ∧ p3) ∨ (((((p3 ∨ p5) → ((p5 ∨ ((p2 ∨ p4) → p1)) ∨ ((True → p3) → True))) → False) → p3) ∧ True)) ∧ ((p2 ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p5) → ((p5 ∨ ((p2 ∨ p4) → p1)) ∨ ((True → p3) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48130936668841962281806598873 : ((((p5 → (False ∧ p5)) ∧ (((p5 → ((p5 → ((False ∨ p5) ∨ p5)) ∨ p1)) → ((p1 ∧ p4) → True)) ∨ (p1 ∧ False))) → (p1 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342818081092814299044595638766 : (p2 → (((p2 ∧ ((p1 ∨ p2) → False)) → False) ∧ (True → (((((((p1 → p1) → p4) ∨ True) → False) ∨ p3) ∧ (p2 → (p2 ∧ p5))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586172367217637505150620831112 : (((((((p5 ∨ (p1 ∨ p5)) ∧ ((p4 ∨ p1) ∨ ((p2 ∨ p2) → (p1 ∧ p2)))) → (p3 ∨ (((p5 ∧ False) ∨ p2) → p5))) ∧ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53768293063880946390571101608 : (((((False → ((p4 ∧ False) ∧ (True → p1))) ∧ p2) ∨ p3) ∨ (p5 ∧ ((p4 ∨ (p1 ∨ ((p5 ∨ p5) ∧ p2))) → (p4 ∧ (p2 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166270060493344653690521841251 : ((p3 ∧ (False ∨ (((((p2 → p2) ∧ p4) ∨ (p3 ∧ p3)) ∨ (False ∨ (False → p1))) ∧ p5))) ∨ ((((True → False) ∧ (p2 ∧ True)) ∨ False) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308457450963120937652238661009 : (p2 ∨ (((((p4 → ((p5 ∨ p5) ∧ ((p2 ∧ (False ∨ ((p4 ∧ (p4 ∨ p4)) ∨ (p1 ∧ p4)))) ∧ p1))) ∧ False) ∨ False) ∨ (p1 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599162017658982493287384498623 : (((((p2 → p3) ∧ (((((p4 ∧ (p5 ∨ False)) ∧ ((p5 → (p4 ∧ (True → p5))) ∨ p3)) → (p1 ∨ False)) ∨ p1) → (p5 ∧ True))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749736981760694615841936030339 : (((True ∧ ((((p2 ∨ p3) ∨ ((False ∨ (False ∧ p3)) ∨ (p4 ∨ True))) ∨ (((((p1 → p1) ∧ False) → p3) ∨ (p4 ∨ p3)) → p4)) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112575543583902424665075839036 : ((((p1 → (((p2 ∨ (((False ∨ (False ∧ (p3 ∨ p5))) → True) → p3)) → (p4 ∨ (True ∨ (p2 → p5)))) → p3)) → p1) → p5) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313703129110172303022711552296 : (p3 ∨ ((p2 ∧ ((p2 → False) ∨ ((p2 ∨ (((p2 ∧ (p5 ∧ (p4 ∧ (p5 → p3)))) ∨ p4) ∨ True)) → (p5 ∧ ((p1 → False) ∧ p3))))) → p3)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ (((p2 ∧ (p5 ∧ (p4 ∧ (p5 → p3)))) ∨ p4) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133626203788409906007498283708 : (((((p3 ∧ p5) ∨ (True ∧ (p1 → ((p5 → ((p3 ∨ (p2 ∧ p2)) → p3)) ∨ ((p2 ∧ p3) ∧ p2))))) → p2) ∧ p4) ∨ ((False ∧ p4) → p5)) := by
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
theorem thm_5_vars_728125570034482911026295148050 : ((((p5 ∨ (p3 ∧ p5)) ∨ ((False ∧ p1) ∨ ((p3 ∨ (p2 → ((p2 ∨ (True ∧ p2)) ∧ (p5 ∨ True)))) → (p1 ∧ (True → (p1 ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38478522011370790109671482726 : (((((p3 ∨ ((p3 ∧ p4) → (p3 ∨ (p1 → p5)))) ∨ (p1 → p3)) ∧ (((True → (p2 → (p1 ∨ p4))) ∨ (p1 ∨ p1)) ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166020481394142882173215867365 : (((p4 ∨ p4) ∨ ((((p3 ∧ (p3 ∨ p1)) → ((p5 → p2) ∨ True)) → (p3 ∧ p1)) ∧ p1)) ∨ (p1 → (p2 → ((False → p2) ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811551656102385605888725845755 : (((p5 → (True → ((p1 ∨ (p1 ∧ (p4 → ((((p4 → ((p3 ∧ True) ∨ (p3 ∧ p1))) ∨ (True → p2)) → p1) ∧ True)))) ∨ (p3 → True)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226013839350831628058605241415 : (((p4 ∧ p2) ∨ p2) ∨ (((p3 → p3) → p4) ∨ (((False ∨ ((True ∧ True) → (p2 ∨ True))) → p3) → ((True → p1) ∨ ((True → p3) ∨ p4))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ ((True ∧ True) → (p2 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748890680648990835857203467368 : ((((p4 → p2) → (((False ∧ (True → ((False → (p1 ∧ (False ∨ p4))) → (p2 ∧ (True → ((p3 ∧ (p1 ∧ p2)) ∧ True)))))) ∧ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58100146090538647086649925953 : (((p1 ∧ p2) ∧ (p3 ∧ ((((p2 → True) ∧ p1) ∧ ((True ∧ (p3 ∧ (p4 → (p3 ∧ p4)))) ∧ ((p2 → p4) ∧ (p5 → p4)))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238058657383818339596502554846 : ((True ∨ p2) ∧ ((p1 → (((True → p5) ∧ ((p2 ∨ (p5 ∨ (p5 → p5))) → (((p2 ∨ p4) ∨ True) ∧ (p2 ∨ (p2 ∨ False))))) ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_263830064149226485355622628254 : (True ∧ ((((((p2 ∨ p5) ∧ p4) ∧ p2) ∨ ((False → True) → False)) ∨ (p2 ∨ (p1 ∧ p2))) → (((p4 ∧ p2) → True) ∧ ((False ∨ True) ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616743485520594769000369609925 : ((((((((p5 ∧ p1) ∧ True) ∧ p2) ∨ ((p5 ∧ p2) ∨ p3)) ∨ ((False ∨ (False ∧ (p3 ∧ ((p3 ∨ p4) → p2)))) → (p2 ∨ True))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_228050017674142376370082117649 : ((p4 ∧ (False ∧ p3)) ∨ ((((((p5 → False) ∨ p1) ∧ p4) ∨ (p2 → (p5 → ((False ∨ p2) ∨ (p4 → p4))))) ∨ p2) ∨ ((p2 → p2) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174891635350746339408683475604 : (((p1 ∧ p3) → (((p5 ∧ p4) ∧ ((p4 ∧ p5) ∧ p5)) ∧ (p5 → (p5 → p5)))) → ((((p1 ∨ (p5 ∧ p1)) ∧ p1) ∨ p3) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58145541279094369269962308320 : (((p2 ∧ p3) ∧ (p1 ∨ ((p5 → (p1 → False)) ∨ (p2 ∨ (((p5 ∧ (p5 ∨ p4)) ∧ (True ∨ ((p2 ∧ p2) ∧ False))) ∨ (True ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149648680339088811849404121028 : ((p4 ∧ (((p5 ∨ (((False ∨ True) ∧ False) ∧ True)) ∧ p2) → (((p3 ∨ ((p2 ∨ True) → p1)) ∨ True) ∧ p4))) ∨ (p2 ∨ (p2 ∨ (p3 → True)))) := by
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
theorem thm_5_vars_42153086194654172505434106784 : ((((p1 → False) → ((p4 → (((p4 → (p4 → p1)) ∨ (p4 → p1)) ∧ ((((p1 ∧ (False ∨ p2)) ∧ p2) ∧ True) ∧ False))) ∨ True)) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3202524135171707652793917027 : ((p4 ∧ False) ∨ (((p3 → p3) → False) → (((p3 ∧ ((p2 → True) ∨ p1)) ∧ ((((True ∧ p5) ∧ p3) ∧ True) → (p3 ∨ p2))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60192419438063010557367410797 : (((p5 ∨ p3) → (p2 ∨ ((((False ∨ False) ∨ p4) ∨ (True ∧ (((p1 ∨ True) ∧ p4) ∧ p5))) ∨ (((False ∨ True) ∨ (p2 → p5)) ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
theorem thm_5_vars_244873064111564298460666651369 : ((p1 ∧ p2) ∨ ((((p1 → (p3 → (((p2 ∨ (p4 ∨ p2)) ∧ (True ∧ p4)) → (p4 → (False ∨ p1))))) ∨ p2) → False) → (False ∧ (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p3 → (((p2 ∨ (p4 ∨ p2)) ∧ (True ∧ p4)) → (p4 → (False ∨ p1))))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h8.left
        let h15 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h8.left
        let h18 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h2
  -- False on the left can always be used.
  apply False.elim h19
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h20 : ((p1 → (p3 → (((p2 ∨ (p4 ∨ p2)) ∧ (True ∧ p4)) → (p4 → (False ∨ p1))))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h26.left
        let h33 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h26.left
        let h36 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h37 := h1 h20
  -- False on the left can always be used.
  apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118716463033153046094814658092 : ((p5 ∨ (((True → (p3 ∧ p3)) ∧ (((p4 → (p3 → (p5 ∨ False))) ∨ p4) ∨ (((p3 ∨ p3) ∨ p1) ∨ p1))) ∨ (p1 → False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699965239751861893976526585176 : (((((p5 ∨ (p1 ∨ (p2 ∧ p2))) ∧ (p3 ∨ ((False → p4) ∧ p5))) → (p5 → ((False ∧ ((p5 → p4) ∨ (p2 ∨ (True ∧ True)))) ∨ True))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149631343468833503722546051496 : ((p4 ∧ (((((((p2 ∨ True) → p1) ∧ p4) ∧ p2) → ((False → p5) → p5)) → ((False ∨ p4) ∨ False)) ∨ p5)) ∨ ((False → (p5 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98810409750952049794133226547 : ((True → (((((True ∨ False) → (False ∨ (((p5 → (False ∨ p1)) ∧ p3) ∨ True))) ∧ p3) ∨ (((True ∧ (p1 ∧ True)) ∧ False) ∧ p2)) ∧ p5)) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156788964730213021130336079770 : (((p2 ∧ (((p2 → (((p2 ∨ p2) → (((p5 → p1) ∧ p5) ∧ p4)) → p5)) ∨ p3) → p4)) ∧ p5) ∨ (p2 → ((True → p5) → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304086352799657629799596242468 : (p1 ∨ ((p5 ∨ ((((p2 → p1) ∧ p3) ∧ ((((p1 ∧ p2) ∨ (False ∧ (p5 ∧ False))) → p1) → (False ∨ p4))) ∧ (p5 ∨ (p1 ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55480349151102910500021845533 : (((((False → p4) → p2) ∨ (False ∨ p4)) → ((p3 ∧ (p2 → (True → p4))) ∨ ((((p5 → p4) → p2) → ((True ∨ p2) ∨ p4)) ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4677752027938800243422339392 : (p5 → (p4 ∨ ((p3 ∧ ((p5 ∨ False) ∧ ((p4 ∨ ((p1 ∨ p4) ∨ p5)) ∧ p4))) → (((p2 ∨ p1) ∧ p5) ∨ (False ∨ (False → True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



