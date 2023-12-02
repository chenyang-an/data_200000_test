variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51979868428555036717463829288 : ((((True → p2) ∧ (((False → (p3 ∨ (p4 → p4))) ∧ True) ∧ ((p3 ∧ False) ∨ p4))) ∨ ((((p2 ∨ p5) → p4) ∨ (p4 → p3)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322606318425836834380728982548 : (p5 ∨ ((p3 → (((((((p3 ∧ p5) ∨ p3) ∧ (p3 ∧ p5)) ∨ p5) ∧ ((True → (p5 ∨ False)) ∨ (p1 ∧ p4))) ∧ p4) ∨ (p3 ∨ p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_756601014856476098880464969334 : (((p1 ∧ ((p1 ∧ (((p5 → False) ∧ (((((p3 ∧ p5) → True) → p5) ∧ p1) → p5)) ∧ p2)) ∨ (True ∧ (((p3 ∨ p4) ∧ False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340874782055357830297404624615 : (p2 → (((p2 ∨ (((((True → (p2 ∧ (True ∨ (False → False)))) ∨ p4) ∧ p4) ∧ True) ∨ p4)) ∧ (((p1 ∨ True) ∨ (False → p3)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184064000798324112789804647251 : (((((True ∧ p4) → ((p3 ∨ p5) ∨ p4)) → (p3 ∧ p4)) ∨ p1) ∨ (p3 → (False → (False ∧ ((p5 → ((p5 ∧ (False → p5)) ∧ p4)) ∨ False))))) := by
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
theorem thm_5_vars_137952092835493941620993590766 : ((p5 ∨ ((p2 ∨ (((((p5 → True) → ((True ∨ p3) ∨ (p2 ∨ p5))) ∧ p1) → False) ∨ (True ∨ (False ∨ False)))) ∨ p5)) ∨ ((p5 ∨ p2) ∧ True)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61209665255369124861227388717 : ((False ∧ ((p1 → p1) → ((True → ((False → ((((True → p2) → True) ∧ (p1 ∨ p2)) ∧ p2)) → (((p5 ∧ p3) → False) → p4))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67645898291989229920725623887 : ((p1 → (p2 ∨ ((p3 ∧ (((p2 ∨ True) ∧ ((((p2 ∨ (p2 ∧ p4)) ∨ p5) ∨ p3) ∨ ((p2 ∨ (p2 ∨ True)) → p2))) → p3)) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_172374296700522642881286732898 : (((p5 ∨ (p3 ∨ ((p2 ∨ p3) ∧ p3))) ∨ (p4 → ((p2 → (p3 ∨ False)) ∨ True))) ∨ (p2 ∨ ((p5 → p4) ∨ (True ∨ ((p1 → p1) ∨ p2))))) := by
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
theorem thm_5_vars_64513491329967733246702545953 : ((p1 ∨ ((((p5 ∨ p1) ∧ ((p3 → p5) ∧ (False ∨ p4))) ∧ (p2 → p4)) ∨ ((p3 → p1) ∨ (((p1 ∨ p4) → (p1 ∧ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114028098975491269508308548623 : (((((p4 → (((p1 → p3) ∨ ((p3 ∧ p3) → (p4 ∨ p4))) → (False ∨ (p1 ∨ p5)))) ∨ True) → p3) ∨ ((False ∨ p4) → p4)) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656481839888306524568721849919 : ((((((p4 ∨ ((False → p1) ∨ ((p2 ∧ True) → p2))) ∧ p4) → ((((p1 ∨ (p5 → p1)) ∨ p1) ∧ True) → (p3 → p5))) ∨ (p2 → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_399300766342690548366348260271 : ((((p1 → (p2 → (((True → ((p3 ∨ ((p5 ∨ p2) → (p5 ∨ ((p4 → True) ∧ p5)))) ∧ p3)) → p3) ∨ ((p4 ∨ p1) ∧ True)))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159881234007299026926227399656 : ((((p3 ∧ ((((True → ((p2 ∨ p1) ∨ ((True ∧ False) ∧ p3))) ∧ p5) ∨ True) → True)) ∧ p4) → False) → ((True → False) → (p4 ∨ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154918441277794544984851260881 : (((((((True → p1) ∧ (False ∧ p3)) ∧ p5) ∧ p4) ∧ (True ∧ (p3 ∨ p1))) ∨ ((p5 → p5) ∨ p5)) ∧ ((False → (False ∧ (False ∧ False))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658490678059784748197462351377 : ((((p1 ∨ (p4 ∨ (((((p3 ∨ p3) ∨ (False → p4)) ∨ False) ∧ p4) ∧ ((p4 → (p1 ∧ False)) → ((False ∧ False) ∨ p2))))) ∨ (p2 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_50644179853456579278723470279 : ((((((((True → False) ∧ (p1 → False)) ∨ p3) → p2) ∧ p2) ∧ (True ∨ (p1 → ((p1 → p1) ∧ p3)))) → ((p4 ∨ (p5 → p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150488525161418905929170509731 : ((((((((p5 → p2) ∨ p2) ∧ p1) → p1) ∨ (p3 ∨ ((p5 ∨ (p2 → p5)) ∨ p4))) → (True ∨ p3)) ∧ p2) → ((True → p5) → (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668575590169810617751105619054 : ((((((p5 → p2) ∧ ((p2 ∧ ((p4 ∨ (False → p3)) ∧ (((p5 ∨ True) ∧ (p5 ∨ True)) ∧ p3))) ∧ True)) ∧ p1) ∨ ((p1 ∨ True) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93195959709646078333962798288 : ((True ∧ (False ∨ (((p3 ∧ (p2 ∨ (p2 ∧ p1))) → (p5 → (p4 ∨ (p5 ∨ p3)))) ∧ (((p5 ∧ p4) ∨ (p1 → p1)) → (p3 ∧ p4))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p5 ∧ p4) ∨ (p1 → p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50813201552057013047205778933 : (((p3 → (p1 ∨ (((True ∧ p1) ∧ (p1 → p5)) → ((p1 ∨ (p2 → False)) ∨ ((p3 ∨ p5) → True))))) → ((p2 ∨ (p2 → p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60654099867710396307395951557 : ((True ∧ ((p3 → (((p4 ∨ ((False ∨ p5) ∨ (((False → p5) ∨ p4) ∨ (True → p3)))) → p4) ∨ p2)) ∧ ((p3 ∧ (False ∨ p3)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57589640886712623960276115255 : ((((True → False) ∧ p4) → ((((True ∨ (((p2 → p1) → p5) ∧ True)) ∧ ((True ∨ p2) ∧ True)) → (p1 → ((False ∨ p3) ∧ p5))) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114727419858477808453829952660 : (((((p1 → ((False → (p1 ∧ True)) ∨ p1)) ∧ p4) ∧ ((p3 ∨ (p3 ∧ True)) ∨ p5)) → ((True ∧ (p4 → p5)) ∨ (p1 ∨ p3))) ∨ (p2 ∨ p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117929465844292537939475900334 : ((p5 ∧ ((p5 ∨ False) ∧ (((p1 ∧ (p5 ∨ p4)) ∧ (False ∨ False)) ∨ (p3 ∧ (((p4 ∨ p5) ∨ (p4 ∧ (p4 → p4))) → True))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655434847354610281801230903501 : ((((((p3 → p3) ∧ ((((((p4 → p5) → (p1 ∨ p2)) ∧ True) ∧ p3) ∨ (False → p4)) ∨ (p1 → p2))) ∨ (p4 ∧ True)) ∨ (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341934494235898975044550015216 : (p2 → ((((False ∨ p2) → p2) → (((p5 ∨ p1) → ((p1 ∨ True) ∨ p5)) ∧ (((False ∧ p1) ∧ p4) ∨ (p1 ∨ True)))) ∧ (p4 ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168084563064586356871324930074 : (((p3 → (True ∨ (p3 ∧ p3))) ∧ (((((p1 ∧ p2) ∨ False) ∧ (p2 → p4)) ∨ p2) → False)) → (p3 ∨ (p3 ∨ (p2 → ((False ∧ False) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p1 ∧ p2) ∨ False) ∧ (p2 → p4)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((((p1 ∧ p2) ∨ False) ∧ (p2 → p4)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148045283717427968635645682633 : (((p1 ∧ ((p1 ∧ p5) → (((p4 → (p3 ∨ p3)) ∧ (True → False)) ∧ ((p5 ∨ p1) → p1)))) ∨ (p4 ∨ p1)) ∨ (((p3 → True) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156699440232140968189191978086 : ((((((p5 ∧ ((((p3 ∧ p5) → True) → p4) → True)) → p3) → True) → (True ∧ (False ∨ p5))) ∧ p5) ∨ ((p3 → ((p2 ∧ False) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135928867166835130997630245847 : (((p1 → ((True → (p3 ∧ (True ∨ (True → False)))) ∧ (p3 ∨ p2))) → ((True → False) ∨ (((p5 ∨ p3) ∧ p1) ∨ p2))) ∨ ((p5 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181352471737503430945858316431 : ((False ∨ (((((False ∨ p5) ∧ True) ∨ True) → p3) ∨ ((False → False) ∧ p1))) → ((((p4 ∨ (((True ∧ p5) → True) → p1)) ∧ p1) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
theorem thm_5_vars_340879686845683030317303618100 : (p2 → (((((((((p2 ∨ p1) ∨ p2) → p3) ∧ ((p2 ∨ p1) → False)) ∨ p1) ∨ p4) → p1) → ((False ∧ (p1 ∧ (p3 → p4))) ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41011137773522133090963813381 : ((((((p3 ∨ (p1 ∨ ((p1 ∧ p2) → ((((p3 ∨ True) → p2) ∧ ((p5 ∧ p4) ∧ p3)) → False)))) ∨ p1) ∨ p3) → (p2 ∨ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244252627270806587727023741011 : ((False ∧ True) ∨ ((p1 ∨ (p2 → (((p1 → (False ∧ p5)) ∨ (p5 ∧ p5)) → ((p3 ∧ (p4 → ((p2 → (p1 ∧ False)) ∨ False))) ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606501213942499900196769531984 : (((((((((p1 ∧ False) ∨ (True ∧ (True ∧ False))) ∨ (p4 → (True ∧ ((p3 ∨ ((False ∨ True) ∧ False)) ∨ False)))) ∨ p4) → p4) ∧ True) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802730030201480044926372357933 : (((p2 → (p2 → ((((((p1 ∧ True) → (True → (True ∧ ((p3 ∨ False) ∧ p3)))) ∨ p5) ∧ ((p1 ∨ p3) → (p2 ∧ p5))) ∨ p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592203875802322777432770502976 : ((((((((True ∨ ((p3 ∧ (False → p1)) ∧ (((p2 → p5) ∧ (p5 ∨ p5)) → p1))) → (p2 → p4)) ∧ p5) ∨ p2) → (p3 → p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167811581366840424481405337893 : ((((((True → p1) ∨ p5) ∧ p1) ∨ (p3 → (p2 → p5))) ∧ (((p3 ∨ True) ∨ False) ∧ p4)) → (p1 → (p2 ∨ ((p4 ∨ False) ∨ (False → p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h4.left
      let h17 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h4.left
    let h24 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306487894530758616165620786343 : (p1 ∨ ((p2 → p1) ∨ (((p3 ∨ ((((True → p4) ∧ p3) ∧ ((p2 ∨ (p1 → (p3 → p4))) ∧ p4)) ∧ ((p4 ∨ p5) ∨ True))) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_113485991399360828215031863893 : (((((True ∧ (p5 → (((p2 ∧ (False → p4)) ∨ ((False → (p5 ∧ False)) → p3)) ∧ False))) ∨ p2) → (p1 ∧ True)) ∨ (p2 ∧ p1)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52281543937837435147058588001 : (((p3 → (((True ∧ p1) ∧ True) ∧ (p4 → (((False ∧ (True ∨ True)) ∨ p2) ∧ p4)))) → ((p4 ∧ ((p3 ∨ p3) ∧ (p4 ∨ p4))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180726545928246422533478608946 : (((p1 → ((p2 → p2) ∧ p2)) ∧ ((p3 → p1) ∨ ((p4 ∨ p5) → p3))) → ((p3 ∨ False) ∨ (p1 ∨ (((p1 → True) ∨ (p4 ∧ p5)) ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249212981190849643066062518781 : ((p4 ∨ p3) ∨ (p1 ∨ ((p5 → True) → (((p5 ∨ (p5 → p4)) → ((p5 → False) ∨ True)) ∨ (True ∨ ((True ∨ True) ∧ (True ∧ (p4 ∨ p1)))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2558766804527117066742556242 : (((p3 ∧ p3) ∨ (True ∧ (p2 ∧ (False ∨ p1)))) ∨ (True ∧ ((False → True) ∧ ((((p2 ∨ p3) ∧ (p3 ∧ (p4 ∨ p1))) ∨ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42536555698255769797740828063 : (((p1 ∨ (((p5 → ((p2 ∨ (((p4 ∧ False) ∧ False) ∨ p3)) → (False ∧ p3))) ∧ (False ∧ (False → (p5 ∨ p4)))) ∧ (p2 → p5))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179738171561161590743939249030 : ((((((p5 ∧ (False → p2)) ∨ p4) → (p1 ∧ False)) ∧ (p4 → False)) ∧ p5) → (p2 ∧ (((p2 ∧ (p4 → p3)) ∨ (p3 ∧ (p5 ∨ p4))) → p3))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ (False → p2)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : ((p5 ∧ (False → p2)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h18
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h1.left
      let h32 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158994938516834817960846862124 : ((p3 ∨ (p5 ∧ (p4 ∧ ((p2 ∧ p1) → (((p1 ∨ True) ∧ p5) → (((True ∧ True) ∧ p3) ∨ p3)))))) ∨ (((p3 ∨ (p5 → p5)) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172656932349392309643059734880 : (((p5 ∨ p4) ∧ (p4 ∧ (((True ∨ ((p3 ∧ (p3 ∧ True)) ∧ p2)) → True) → p3))) ∨ ((((p1 ∧ p5) ∨ p4) ∧ (True ∧ p4)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187552447945470687439199856749 : ((p2 ∨ ((False → False) ∨ (True → ((p1 → p1) ∨ (p1 → p3))))) → (p3 → (((((p3 ∨ p4) ∨ (p3 → p3)) ∧ p2) ∨ p5) → (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230488665805234782850309610015 : (((True → False) ∧ p1) → (((False ∨ p1) ∧ ((p4 → ((p5 ∨ p3) ∧ (((True ∨ (p4 ∧ (p3 ∧ True))) → p3) → (p2 ∨ p1)))) → False)) ∨ p5)) := by
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
theorem thm_5_vars_248464814525086176114262846891 : ((p2 ∨ p5) ∨ (((((p1 ∨ p4) ∧ False) ∧ True) ∧ (False ∨ p4)) ∨ (p4 ∨ ((((False → True) → p4) ∨ (p3 → ((p1 ∨ p2) ∨ True))) → True)))) := by
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
theorem thm_5_vars_316924867642427105134886521999 : (p3 ∨ (p2 → ((True ∧ (False ∨ ((p5 ∧ ((((p2 → (p2 → p5)) ∨ ((p4 → (p5 ∧ p2)) → p1)) → False) → p4)) ∧ p4))) ∨ (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153301012659375640497266877654 : ((p1 ∨ (((((p2 ∧ (((p5 ∨ p2) ∨ p5) → (p5 ∧ False))) → p3) ∨ p4) → p1) ∧ ((True ∨ p3) → p4))) → (p1 ∨ ((p4 → True) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (((p2 ∧ (((p5 ∨ p2) ∨ p5) → (p5 ∧ False))) → p3) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777013116341734250359016090112 : (((p1 ∨ ((((((False → p2) ∧ p3) → p5) → ((((True ∧ (p3 → p3)) ∧ p4) ∧ p1) ∧ ((True ∧ p2) → True))) ∧ p5) ∨ (p3 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40317002371635912429896293194 : (((((p2 ∧ (p4 ∨ ((((p5 ∨ p3) ∧ p5) ∨ p1) ∨ (True ∨ (p2 ∨ ((False ∧ ((p3 ∨ p2) ∧ True)) ∧ p3)))))) ∧ p4) ∨ p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159011013417738942246692734798 : ((p4 ∨ ((((False ∧ (True ∧ (True ∨ p2))) ∧ ((p5 → p5) ∧ True)) → ((p2 ∨ p4) ∧ p5)) → p5)) ∨ ((True ∧ False) → ((p3 ∧ False) → p3))) := by
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
theorem thm_5_vars_226627992093621360759700104663 : (((True ∧ True) → p4) ∨ (((p2 → (p2 ∧ p2)) → (((((True ∨ False) ∧ (False ∧ p3)) ∨ p1) → p2) → ((False ∨ True) → (False ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587309542273398742131377986796 : ((((((((p2 ∨ p1) → ((True ∨ True) → p4)) ∧ (((p3 → p1) → p1) → ((p4 → p1) → (p5 ∧ (False ∧ p2))))) ∧ p3) ∨ True) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119034545587711163890674457109 : ((p1 → (((p4 ∧ (p3 ∨ (((((p5 → p2) ∧ (p1 → p3)) ∧ p4) ∨ p1) ∨ (p1 → (False ∧ (p5 → False)))))) ∨ False) ∧ True)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116177440822353908326519215571 : (((p2 → (p2 → p1)) ∧ (((((False ∨ False) ∧ False) ∧ ((((p4 ∧ p5) ∨ p4) ∨ (False → (p2 ∧ p4))) → p3)) ∧ p2) ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650139418842279267647063006696 : ((((((p1 → ((((p1 ∧ p1) ∨ True) → (True ∨ True)) ∧ (p5 → p2))) → (p3 ∧ p4)) ∧ (p4 → ((p3 ∧ p5) ∨ p2))) ∧ (p4 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45144552568063769176018997047 : ((((p5 → p2) → (((((((False ∨ p4) ∧ p2) ∨ ((p3 ∧ (p5 ∧ p4)) → False)) ∧ (p5 ∨ p5)) ∧ p2) ∨ (True → p3)) ∨ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704493945899627346838383953770 : (((((p1 ∧ p5) ∧ (p2 ∨ (p2 ∨ ((p4 → False) ∨ p5)))) → (p2 ∨ (p1 ∧ (p5 → ((p2 ∨ (((False ∨ True) ∧ True) ∧ p5)) ∧ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
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
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
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
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116492072475130550232545298200 : (((p2 ∧ p5) ∧ ((True ∧ ((((p1 ∧ (p5 → p3)) ∧ (p4 ∨ (True → True))) ∧ p3) → (p2 ∧ True))) ∧ (p5 → (p5 → p2)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49887734230846182033774842095 : ((((((p3 ∨ (((True ∧ True) ∨ p2) → True)) ∨ p4) ∨ (p3 → (True → ((p3 ∨ p2) ∨ True)))) ∨ p2) ∧ ((p5 ∨ p3) ∨ (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306102076278008265045626275427 : (p1 ∨ (((p3 ∨ False) → p3) ∧ (((p3 ∧ ((False → True) → ((p4 ∨ p3) → p1))) ∧ p3) ∨ ((((p4 ∨ p1) ∨ True) → False) → (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305009195082083582274284247850 : (p1 ∨ ((((p4 → (p5 ∨ (True ∧ (p3 ∨ p5)))) → p2) → ((p4 ∨ (p2 ∧ True)) → ((p2 ∨ p1) ∧ (p4 ∨ p1)))) ∨ (p2 → (p4 ∨ p2)))) := by
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
theorem thm_5_vars_61130742296442628459002303601 : ((False ∧ ((((p1 ∨ p3) ∨ ((False ∨ True) ∧ True)) → p4) ∨ ((p1 ∧ (((p4 ∨ (p2 ∧ (p3 → p5))) ∨ p4) → p2)) ∨ (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342088746214736955685097404476 : (p2 → ((p3 → ((((p2 ∨ (True ∨ (False ∨ False))) ∧ ((p5 ∧ False) ∧ (((p1 → p4) ∧ p5) → False))) → p4) ∧ p1)) → (p5 → (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113538599984142278780627023910 : (((((p4 ∨ (p5 ∨ p4)) ∧ p1) ∨ (((p2 → p4) ∨ (p1 → p4)) ∨ (False → ((False ∨ p5) → (p3 ∨ True))))) ∨ (False → True)) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115335288368401127968030063525 : (((True ∨ ((((True → p1) → False) ∨ (p1 → p3)) ∨ p1)) → (p3 ∨ (((True ∨ ((p5 ∧ p2) ∧ p1)) → (p2 → p3)) ∧ False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115142236858997568216906431911 : (((p1 ∧ ((((True ∨ (p2 ∧ p2)) → p5) ∨ p5) ∧ (p3 → p4))) → ((True ∨ True) ∧ (((False → p5) ∧ (True → False)) ∨ p5))) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (True ∨ (p2 ∧ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47340928034256074527640709769 : ((((p2 ∨ p5) ∧ (p3 ∨ (p1 → (p2 ∨ (p3 ∨ ((p1 ∧ ((p5 → p5) ∧ False)) → ((True → p5) ∧ (p1 ∧ p4)))))))) ∨ (p4 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51888751711389597729183625614 : ((((((((p1 ∧ (p1 ∨ p4)) ∧ True) ∨ p3) → p5) ∨ (p2 ∧ (False ∧ True))) → p1) ∨ (((False ∨ p2) ∧ ((False ∨ False) → p5)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55992171788515144165826480528 : ((((p4 ∨ (p1 ∨ p5)) ∧ p4) ∨ ((True ∨ (p5 ∧ p5)) ∧ (p2 ∨ ((p2 → ((p4 → (p5 ∧ True)) ∧ p5)) → ((False ∨ False) → p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208419506172872611350585298174 : (((p2 ∨ p3) ∨ (p1 ∧ (p5 ∨ p1))) → ((p1 ∨ ((p1 ∨ p5) ∧ (((((p4 → (p4 ∧ p5)) → (True → p4)) → p5) → p3) → False))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
theorem thm_5_vars_166486586486838971065838671385 : ((p3 ∨ ((p2 ∧ (p5 ∨ (p1 ∧ (p1 → p3)))) ∧ (False ∧ (p4 → (p4 ∨ (p5 ∧ p2)))))) ∨ ((p3 → (((True ∧ False) ∧ False) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90936016308364780336389608027 : (((True → p3) ∧ ((p3 ∧ ((False → p1) ∧ (((p5 → True) → (p3 → (False ∧ ((p5 ∧ (p1 ∨ (p4 ∧ False))) → True)))) → p3))) ∨ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118651830067240730842901574539 : ((p4 ∨ (p3 ∧ (((((p1 ∨ (False → False)) → (p4 ∧ False)) ∨ (p3 ∧ ((True → (True ∧ (False ∨ p3))) ∨ p3))) ∨ False) ∨ p2))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743041410812473282983033654765 : ((((p4 → False) ∨ ((p3 → (p5 → ((((True → p5) ∧ p1) → (p3 ∧ ((p3 → False) ∧ (p5 → True)))) ∨ p5))) → ((p3 ∨ p5) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213364232822938648781868685378 : (((p4 ∧ (p4 → True)) ∧ p5) ∨ ((((p5 ∨ p5) ∧ p4) ∧ ((p1 → True) ∨ (p1 → (False ∨ False)))) ∨ ((True ∨ p2) ∧ ((False ∧ p1) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_805551123434855603353990117823 : (((p3 → (p5 ∨ ((p4 ∨ (p4 → ((True ∧ ((True → True) ∧ (p2 ∨ (p2 → (False ∨ ((True → p4) ∧ p4)))))) → (p1 ∨ p1)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606754616743385523846541191090 : ((((((p2 → ((p2 ∧ (p3 ∧ (False ∨ p1))) ∧ (((p3 ∨ (p1 ∧ (p2 ∧ (p5 ∧ p4)))) → True) → p5))) ∨ (False ∧ True)) ∧ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69671927821913574845064855943 : ((((p3 → (((False → (((False ∨ (p3 → p5)) ∨ (p2 ∨ p3)) ∧ p1)) ∨ (True → (((p2 ∧ p3) ∧ p3) ∧ p5))) ∧ False)) ∧ p3) ∧ p4) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112084060977590168128937184574 : ((((p1 ∨ p3) ∨ (p5 ∨ ((p1 ∧ p3) ∨ (((p2 ∨ (False ∨ (p5 ∧ p4))) ∨ (p3 ∧ (p2 ∧ (p2 → p3)))) → p2)))) ∨ True) ∨ (False → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615069400442694211991900588091 : (((((p5 ∨ ((p4 ∨ p2) → (True → (True ∧ ((False → p4) ∧ (True ∨ ((p4 ∨ p1) → p3))))))) → (False ∧ ((True ∧ p3) → False))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_158075148068154173217045172523 : ((((p2 ∨ (p1 ∧ True)) ∧ (False → True)) → (p4 → ((p2 ∨ (((True ∧ p5) → p3) ∧ False)) ∧ p3))) ∨ ((True ∧ ((p5 ∨ p4) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224272288295251058413715809177 : ((False → (False ∧ p4)) ∧ (((p1 ∨ p2) ∨ p4) → ((p5 ∨ (((p3 ∨ (p5 → p4)) ∧ (p5 ∧ (False ∨ p1))) ∨ (True ∨ p3))) ∨ (p2 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152659238191105876456750370151 : (((p2 → False) ∧ (((True ∧ (((((p5 ∧ p4) ∨ p2) ∨ p1) ∨ False) ∧ (p1 ∨ (p2 → False)))) ∨ p5) → p2)) → ((p1 ∨ (p3 ∧ p2)) → p3)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True ∧ (((((p5 ∧ p4) ∨ p2) ∨ p1) ∨ False) ∧ (p1 ∨ (p2 → False)))) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213806314069330268993258087837 : (((p3 ∧ (True ∧ p2)) ∨ p1) ∨ ((p5 ∨ (((p5 ∨ p2) → ((p5 → (((True ∨ (p1 ∨ False)) ∨ False) → (p4 ∨ p2))) ∨ p1)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340704347353527196530025473886 : (p2 → ((((True ∨ (p4 ∧ ((p1 ∧ p2) ∨ ((p3 ∨ (p3 ∧ ((False ∧ (True ∧ True)) → p5))) → p1)))) → (p5 → (False ∨ p1))) ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248148490841887573528743767867 : ((p2 ∨ False) ∨ ((True ∧ ((p1 ∨ (p3 ∧ ((p2 → ((p2 ∧ p3) → ((p1 → True) ∧ False))) → p4))) ∨ (p1 ∧ (True ∨ p1)))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351828897034249350415874297649 : (p4 → ((p4 ∧ ((p2 ∧ ((p4 ∧ p3) ∨ ((p1 ∨ p5) ∧ p3))) ∨ p1)) ∨ (False → (False → ((p1 ∧ False) → (((p4 → p2) ∨ p2) → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53832916903435697034854959574 : ((((((p5 ∧ p3) ∧ p2) ∧ False) ∧ ((p2 ∨ p2) → p1)) ∨ (p4 ∨ (((p4 → p3) ∧ ((p5 → p2) → (False ∧ p1))) → (p3 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42062371547596547251285489994 : ((((p4 ∨ p2) ∨ (((p1 → (False ∨ ((p2 → p2) ∨ (p3 → (((False → (p5 ∧ p3)) ∧ False) ∨ False))))) ∧ p4) → (p2 ∧ True))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303985283231745282595354249631 : (p1 ∨ (((p5 ∨ p3) ∧ (((p1 ∧ p5) ∨ ((p4 ∨ p4) ∨ p1)) ∨ ((((False ∧ p5) ∨ ((p1 ∧ p3) → p2)) ∨ p5) ∨ (p4 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56207819819952984941774553044 : (((False ∨ (False ∨ (p4 ∧ p2))) ∨ (((p5 → False) ∨ (((False → p3) ∨ p2) ∧ p4)) ∨ ((p4 → p2) ∨ ((False → p5) ∨ (False ∨ p3))))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158592701806439819313937018668 : ((False ∧ (((((p1 → (True ∨ (p1 → True))) → p2) ∨ p5) ∧ ((p3 ∨ (p4 ∨ p2)) ∧ p5)) ∧ p1)) ∨ ((True ∨ ((p5 ∧ True) ∨ p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252412301811694858073176565398 : ((p5 → False) ∨ ((((p4 ∨ p3) ∨ p3) ∧ (p3 ∧ (p5 ∨ p4))) ∨ ((((p4 ∨ ((p3 ∨ False) ∧ (True ∧ False))) ∧ True) ∨ (True ∧ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



