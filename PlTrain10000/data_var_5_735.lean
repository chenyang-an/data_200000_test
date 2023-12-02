variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208573349137370781031547013652 : (((True → p1) → ((p4 ∨ p5) → False)) → ((((True ∧ (p4 ∨ (p1 ∨ (((p4 → p5) ∨ p5) → p3)))) → p2) ∧ (p3 ∨ (p1 ∧ p5))) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (True → p1) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725646512719299691712559767218 : (((((p5 ∧ p1) ∧ False) ∨ ((p2 ∧ ((p3 ∨ ((True ∧ ((True ∧ p3) ∨ True)) → False)) ∧ (p2 → ((p4 ∧ (p2 → p3)) ∨ False)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356044147426767481445027686470 : (p5 → ((p4 ∧ ((False → ((True ∨ p2) ∨ (p1 ∨ p5))) → ((p4 ∧ (p5 ∨ (p5 ∧ p1))) → (p4 ∧ False)))) ∨ (((p3 ∧ p2) ∨ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86635036689796759823826295412 : ((((p5 → (p4 ∧ p5)) ∧ ((p5 ∨ True) → False)) ∧ (p2 ∧ (p5 → (((p5 ∧ True) ∨ (((p3 ∧ False) ∨ p2) ∨ p5)) → (p3 → True))))) → p3) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192582236850083333521488762892 : (((False → (((p1 ∨ p4) → p1) ∨ (p4 → p5))) ∨ p4) → (True → (((((p5 → (p1 ∧ p4)) ∧ (p1 → (p4 ∨ False))) ∨ p1) ∨ True) ∨ True))) := by
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
theorem thm_5_vars_242320896110296935191261315522 : ((p2 → p2) ∧ (((((p4 → False) ∧ (p2 ∨ p2)) ∨ (p3 ∧ p5)) ∨ ((p4 ∧ ((p2 ∧ (p1 ∨ p4)) ∧ p5)) ∨ True)) ∧ ((True ∧ p4) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339118872726074985879219092203 : (p1 → (p1 ∧ (((p3 ∨ True) ∧ ((((True → (False → p5)) → False) ∨ (True ∧ (False ∨ p1))) ∨ ((p3 → (p1 ∧ p1)) ∧ (True → p4)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726856297003585159346915848302 : (((((p3 ∨ p1) → p2) ∨ (((((p4 ∧ p1) → p4) ∧ (p5 → ((p3 → (False ∧ (p5 → p3))) → (p5 ∧ (p4 ∧ p4))))) ∧ p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876861937638701722369605050534 : (((((((p3 ∧ (p2 → p2)) ∨ p1) → (((True → (p3 → True)) → p4) ∧ False)) ∧ ((p1 ∧ p5) ∧ (p5 → (p2 ∧ p3)))) ∧ (p3 → p5)) → p3) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 ∧ (p2 → p2)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784458302716449151205272000283 : (((p3 ∨ (p5 ∧ ((False ∨ ((p5 → p5) ∨ (((((True → p5) ∧ p4) → True) → p1) ∨ (True ∨ p3)))) ∧ ((p3 ∨ (p4 ∨ False)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65553869898809453428213518376 : ((p3 ∨ (p1 → (((((((((p2 → p5) ∨ (p2 ∨ p5)) ∧ (True ∨ p5)) ∨ p3) → p4) ∨ (True → p4)) ∨ p2) → (p2 ∨ False)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164966311251812060892895065534 : (((((p1 ∨ True) → ((False ∨ ((True ∨ p4) ∧ (True ∧ p4))) ∨ p5)) ∧ (p4 → p2)) → False) ∨ ((False ∧ (p2 ∧ ((p1 → p5) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322354238692765849314212267441 : (p5 ∨ ((((p2 ∨ (False ∧ (((p5 ∨ (((p4 ∧ p3) ∧ True) → p5)) ∨ ((False ∨ p1) ∧ p1)) ∧ True))) ∧ p2) ∨ ((False → p4) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_309800397517416611753068568545 : (p2 ∨ (((((p2 → ((p4 ∧ True) ∧ False)) → p2) ∧ p2) → (p3 ∨ ((p4 ∧ True) ∧ ((True → p2) ∧ p2)))) ∨ (p5 → ((p5 ∨ p4) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2699199122627532464707134022 : (((p1 → p4) ∧ ((p1 → p1) → False)) → (p5 ∨ ((p4 ∧ (p2 ∧ (((p5 ∧ p4) ∨ p4) → ((p5 → p1) ∧ p2)))) → (False ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116711011570615123431783006012 : (((p1 ∧ p4) ∨ ((False ∧ (p3 ∨ (((p3 ∧ False) ∧ (p5 ∨ (p5 ∧ p4))) → (p1 → False)))) ∨ (False ∨ ((True ∧ p3) ∨ p1)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147928865075702189138259448403 : (((((((p1 ∧ p4) ∧ p2) ∨ p2) ∨ p4) ∧ (((p3 ∧ p1) ∧ ((False → p4) ∧ False)) ∧ False)) ∧ (p2 ∨ p4)) ∨ (((p3 ∧ False) → p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148009933965141789716093016649 : ((((True ∨ ((p5 ∨ (True → p5)) ∨ (p1 → (p2 ∨ (p2 → (p5 ∧ p1)))))) → (p5 → p2)) ∨ (p4 → p1)) ∨ ((p2 ∧ p4) → (p5 ∨ p4))) := by
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
theorem thm_5_vars_116367179891473440086647720137 : ((((p4 ∧ False) → p2) → (p4 ∧ ((True ∨ p5) → (True ∧ (p4 ∧ ((p3 ∧ (False ∨ ((False → p3) ∧ (p3 ∧ True)))) → p2)))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610469830863032427233789359972 : ((((((p2 ∧ (((((p4 → ((p3 → p3) ∨ (False ∧ True))) ∨ (p3 ∧ True)) ∧ p1) → (p2 → False)) ∧ (p2 ∧ True))) → p3) → p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159167711113847695444021289110 : ((p1 → ((((False ∨ p4) ∨ (p5 ∨ (p2 ∧ (False ∧ p3)))) ∧ p1) ∧ (p2 → (p3 ∨ (p3 → p2))))) ∨ ((((False ∧ p4) ∨ p5) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111425422978064265505388828329 : (((p4 ∨ (((p1 → (p3 ∧ (p5 → (((p3 ∨ False) → p4) ∧ ((False ∨ ((True ∨ p2) → p2)) ∨ p2))))) ∧ p3) → p1)) ∧ p4) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54623459850635341479014757164 : (((((p5 ∧ (p5 → (False ∧ p3))) ∨ p3) ∧ True) → ((p4 ∧ p1) ∨ (False ∧ (((((True → p2) ∧ p2) ∧ p4) ∨ True) → (True ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168240346082955926245284083498 : ((((p3 → p1) ∨ p4) → ((p5 ∧ (p2 ∧ (p1 ∨ True))) ∧ (p1 ∧ (p4 ∧ (True ∨ p2))))) → (((True ∧ p4) ∧ p2) → ((p3 ∨ True) ∧ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((p3 → p1) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117214963935847949583636438739 : ((True ∧ ((p1 ∨ (p4 → p4)) ∧ (((((((p4 → p3) → (True ∨ p4)) ∨ True) ∧ p2) ∧ p2) → (p1 → (p2 → p5))) → p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53127316609242564547232110699 : ((((((p2 ∧ (False ∧ (p5 → False))) ∨ (True ∧ p2)) ∨ p2) ∧ False) ∨ (((p5 → p4) ∧ False) → ((True → (p1 → p5)) ∧ (True ∧ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198728738941906170949408797863 : ((p5 ∨ (p5 ∧ ((p1 ∧ p4) ∧ (p1 ∧ p2)))) ∨ (((False → p5) → p4) → ((p4 → ((p2 ∧ True) ∨ (True → p5))) ∨ (p4 ∧ (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176657838564271526892393409601 : (((p4 ∧ (p3 ∨ (p1 ∧ False))) ∨ ((False ∨ (False ∨ (True ∧ False))) → p2)) ∧ (p1 ∨ (False → (((False ∧ p4) ∧ p2) ∧ ((p3 ∧ p1) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h8
  -- False on the left can always be used.
  apply False.elim h8
  -- False on the left can always be used.
  apply False.elim h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321308298141588931220257028623 : (p4 ∨ (p5 ∨ (((True ∧ (p3 ∨ (((p1 ∨ p1) → (False ∨ p1)) ∨ p2))) ∧ ((p4 ∨ (p4 ∨ (p5 ∧ p2))) ∧ True)) ∨ ((False → p2) → True)))) := by
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
theorem thm_5_vars_134029664747632072312790762410 : ((((((False → (True → p4)) → (p2 ∧ (((p1 → False) ∧ ((p5 ∨ p3) ∧ True)) ∨ p4))) ∧ (p1 ∨ True)) ∨ True) ∨ True) ∨ ((False → p2) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62769442517291972712781405133 : ((p4 ∧ ((((((p1 → p2) ∨ p1) ∨ (p1 ∧ p5)) ∨ ((p5 ∨ p4) → ((True → False) ∧ (False ∧ p5)))) ∧ p3) → (p2 ∧ (p5 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48664707738637650174952778229 : ((((((True ∧ (p5 ∧ ((p2 ∨ p4) ∧ False))) ∧ p2) ∨ (False → False)) ∨ (p2 ∨ ((p2 → (p3 → p2)) → p1))) ∧ (p5 ∨ (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688373762376180868030675762711 : ((((False ∧ (((False ∧ True) → (False ∨ p5)) ∧ ((((p4 ∧ False) → p3) → p2) ∨ True))) ∧ (p3 ∧ ((((p1 ∨ p3) → p5) → p1) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216108782911132645259883493627 : ((True → ((p4 → p3) → False)) ∨ (((p5 ∨ p4) ∨ (((p4 ∨ (False ∧ ((p5 ∧ p3) ∨ (p3 → (p3 → p4))))) ∨ (p2 ∨ False)) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_117460768717058604062372037989 : ((p1 ∧ ((p1 → p4) ∨ ((((p4 ∨ True) ∧ p5) → p3) ∧ (p2 ∧ (p3 → (((True ∧ False) ∧ (p4 ∧ p3)) ∧ (p3 ∨ False))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223391750750927795174210278801 : ((True ∨ (p5 ∨ False)) ∧ ((((p1 ∧ p1) ∨ (p3 ∨ (True ∨ (True ∨ True)))) ∧ (p3 ∧ p2)) → ((False ∨ (((False ∧ p4) → p2) → p2)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h3.left
        let h16 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h3.left
          let h20 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h3.left
          let h23 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126890757194745976537436526474 : ((p5 ∧ (p1 → (False → (((p1 ∧ (p4 → p3)) ∧ (p4 ∨ ((p1 → p4) ∨ ((p4 ∧ p3) ∨ (p2 ∨ (p4 ∨ p5)))))) → p1)))) → (p3 ∨ p5)) := by
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
theorem thm_5_vars_73820539722129235845113926906 : (((((p4 ∧ p2) ∧ ((True ∧ (p1 → p3)) ∧ ((p2 ∨ p1) ∨ p5))) ∧ (True → (p4 ∧ ((p4 ∨ True) → (True ∧ (p5 ∧ p3)))))) ∨ False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : (p4 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h24 := h12 h23
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h27 := h4 h26
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
      have h29 : (p4 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h28, we can now drive its conclusion.
      let h30 := h28 h29
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646827829009229445135989156579 : ((((p2 → (((p5 ∨ p2) → (p5 ∧ (p4 → p2))) → ((False ∨ (p3 → ((((p5 → p5) ∧ (p5 → p3)) ∧ True) ∨ p2))) → p5))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337055707015148692301705059799 : (p1 → (((p5 → (((p1 ∧ ((((((True ∨ (p2 ∨ p5)) → p1) → p5) ∨ p1) → p1) ∨ p1)) → (p2 ∧ p1)) ∨ False)) ∨ p4) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250914148594529110364230525463 : ((p1 → p3) ∨ (p2 ∨ ((p4 ∧ (p4 ∨ p3)) → (p5 ∨ (((p3 ∧ p3) → (p3 → (p5 → ((p4 → (True → True)) → (False ∨ p5))))) ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684148592737640336933883154934 : (((((((p1 ∨ ((p4 ∧ (p1 ∧ p2)) ∧ (p4 ∧ (p1 ∧ p3)))) → p4) → p3) ∨ (True ∨ p5)) ∨ (((p5 ∨ False) ∧ p4) ∨ (True ∧ False))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324174190028419784342402619518 : (p5 ∨ (((p4 ∧ False) ∧ ((p1 → p4) → (True ∧ (False → p3)))) ∨ ((p3 → False) ∨ ((((p5 ∧ p4) ∧ (p2 ∧ p3)) ∧ (p3 ∨ p2)) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39038275870775584272708602883 : ((((p5 → p1) ∧ (((p4 ∧ (False → (((p1 ∧ p1) → (p1 ∧ p5)) → (p4 ∧ p3)))) ∨ (p5 ∧ ((p3 → p3) → p1))) → p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149849312771186114348071198126 : ((p1 ∨ (p5 ∧ (((((p5 ∧ (True → ((p4 ∧ p1) → (True ∨ p4)))) → False) ∨ p3) ∧ p3) ∨ (True ∨ p5)))) ∨ (True ∨ (True ∨ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200802863386034119561748467048 : ((p5 ∧ ((((False ∨ True) → p1) ∧ p3) → True)) → ((p1 ∨ ((True ∧ True) ∧ (((p1 → ((p2 → p3) ∧ False)) → p4) → p2))) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113765251811221622084300924600 : ((((((False → (p4 → p2)) → False) ∨ False) → ((p5 ∧ (True ∨ (p3 → (p5 ∨ ((p4 ∨ p2) → p2))))) ∧ p5)) → (p2 ∧ p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230888192381608760450263075757 : (((p2 ∧ p1) ∨ p1) → (((True ∧ p5) ∨ (((p4 ∧ p1) ∧ False) ∨ (p4 → p1))) → ((p4 ∧ p4) ∨ (True ∨ (p2 ∧ ((p3 ∧ p2) ∧ p2)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259968898521873439993023222584 : ((p1 → p5) → (p3 → ((((p5 ∧ p4) ∨ (p4 ∧ (((False ∨ p4) ∨ p5) ∧ p2))) ∧ ((((p3 → p5) ∨ (p3 ∧ p1)) ∧ p2) ∧ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61546052387779806893523145613 : ((p1 ∧ (((p1 → ((((p1 ∨ p2) ∨ True) → False) ∨ p5)) ∧ p2) ∨ ((p2 ∨ ((((p4 ∨ p1) → p3) → True) → p2)) ∧ (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114782418026486099985863826479 : ((((p3 ∨ ((p3 ∧ p2) ∧ ((p1 ∨ True) ∧ (p5 ∨ (p4 → False))))) ∨ p1) ∧ (p2 ∧ (False → (((p2 → p2) ∨ p5) ∧ p1)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127663253651534602338491573215 : ((p5 ∨ ((True → (((False ∧ ((p3 ∧ p5) ∨ p5)) → (p2 → False)) → True)) → (p2 ∧ (((False ∨ p3) ∧ (False → p5)) ∧ False)))) → (p1 ∨ p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True → (((False ∧ ((p3 ∧ p5) ∨ p5)) → (p2 → False)) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_516451434027282111863851960145 : ((((p3 → p5) ∨ (p2 ∨ ((True → p3) → (((((p5 → p3) ∨ ((p1 → True) ∨ (False ∨ p4))) → (p2 ∧ True)) → (p5 ∧ True)) ∨ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722206662334121509249233708144 : ((((p5 → ((p3 → True) ∧ True)) → ((((p4 → ((False → (p5 → (p4 ∨ p3))) → p2)) ∨ (p5 ∨ ((p5 ∨ True) → p5))) ∧ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171926197416104343048483409017 : (((((p2 ∨ True) ∧ ((True → p3) ∨ (p3 → (p1 → True)))) ∧ False) ∧ (False ∨ p4)) ∨ ((((p3 ∨ p4) → p4) → p4) ∨ (False → (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_52697125663216037213949287569 : (((p1 → (True → (p4 ∨ (((p3 → True) → (False ∧ p2)) ∨ (p1 ∧ True))))) ∨ ((p1 ∨ p2) ∨ (False → ((False ∧ False) → (p1 ∨ p5))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299404173375162211412158714143 : (False ∨ ((p1 ∧ (p1 ∨ (p5 ∨ ((((((p4 → p1) ∧ (p3 ∧ (((p4 ∨ (True ∨ p3)) → p4) → p5))) → False) ∧ True) ∨ True) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674269368932599131440145123916 : ((((True ∨ ((p1 ∧ (p4 → (p2 → True))) ∨ (p3 → (False ∧ (((((p3 ∨ p5) → True) ∨ p4) ∨ p2) → p4))))) → (p5 ∨ (p5 ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345686802004432274049188975227 : (p3 → ((p4 ∨ (((p5 → (p1 ∨ ((p2 ∨ ((((p5 ∧ p4) → True) → p3) → (p3 → (p2 ∨ False)))) ∨ p4))) → (p3 ∧ False)) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1082019934288212995938613985 : ((((p4 → (True → (((p2 ∨ p4) ∧ (p5 ∨ (True → ((p4 ∧ False) → p3)))) → False))) ∧ p5) ∧ (((p1 ∨ p5) ∨ p5) ∧ p4)) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : ((p2 ∨ p4) ∧ (p5 ∨ (True → ((p4 ∧ False) → p3)))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((p2 ∨ p4) ∧ (p5 ∨ (True → ((p4 ∧ False) → p3)))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h24 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h25 := h4 h24
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : ((p2 ∨ p4) ∧ (p5 ∨ (True → ((p4 ∧ False) → p3)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h29 := h27 h28
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152074763886230211600758362381 : (((True → (p3 → ((p1 ∧ ((p5 → True) ∨ False)) → p2))) ∨ ((p4 ∨ (p1 ∨ (p3 → (p2 ∧ p4)))) → p5)) → ((False ∧ False) ∨ (p1 ∨ True))) := by
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
theorem thm_5_vars_302767830705946832381249142790 : (False ∨ (p4 ∨ (((p2 ∨ (False ∨ p5)) ∨ p3) ∨ (p2 → (((p5 ∨ (((True ∨ p4) → ((False → p2) → p4)) ∧ p1)) ∧ p4) ∨ (p2 ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206800135811808993319559245549 : ((p4 → (p3 → (p1 → (True ∧ False)))) ∨ (p4 ∨ ((p3 → ((p2 ∨ p1) ∨ ((((True → True) → p4) ∧ (p5 → False)) ∨ p3))) ∨ (True → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264572816092519335257842296745 : (True ∧ ((p3 ∧ (False ∨ False)) ∨ ((((True ∨ (p4 ∧ True)) ∧ ((True → True) → (((True → p4) → p3) → p3))) → (True → False)) ∨ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622224534209263407427661995493 : ((((p2 ∧ (p2 ∨ (p2 → ((p1 → (p3 ∧ (False ∧ p4))) → (p3 → (((p4 ∧ p4) ∧ (p2 → (p5 ∧ p1))) ∨ (p5 ∨ True))))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178333166620374672379124959385 : ((((p4 ∨ ((p5 ∧ p4) → p1)) → (p2 ∨ (p1 → False))) ∨ (p1 ∨ p4)) ∨ (True ∨ (((False ∨ (p4 → True)) → (p3 ∨ False)) ∧ (p2 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706948230278379539594853202417 : ((((((p2 → (False ∧ False)) ∧ (p2 → True)) ∨ p3) ∨ (((((((True → ((True ∨ False) ∧ p4)) → p3) ∨ True) ∨ p4) → p5) ∨ p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45110020809719883215663111241 : ((((p3 ∨ True) → (((p3 → True) ∧ (False ∧ (True → (((p1 ∨ True) ∨ True) ∨ ((p5 ∨ (p1 ∨ False)) → True))))) ∨ (p3 → True))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304679647693830153038643980325 : (p1 ∨ ((((p3 ∨ p5) ∧ ((((((p2 ∧ ((p1 ∧ p1) ∨ p2)) ∧ p4) ∨ p5) → p3) ∨ p2) ∨ ((p1 ∨ False) ∨ p2))) ∧ p4) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346920112850390631109530875077 : (p3 → ((p2 ∧ (((p2 → (p4 ∨ p2)) ∧ (p2 ∧ (True → ((p5 → False) → (p5 ∧ False))))) ∧ p2)) ∨ (((p4 → True) ∨ (p3 ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164991306430408793876596117237 : (((((False ∨ (p5 ∨ (((p1 ∨ p5) ∨ p2) → False))) → p2) → ((p5 ∧ True) ∨ True)) → p2) ∨ ((p1 → (((p5 → True) ∧ False) ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64916414213807197338291528898 : ((p2 ∨ (((p5 → (p2 ∧ False)) ∨ (p4 → ((p2 → (((p3 ∨ p3) ∧ p3) ∨ False)) ∧ p2))) ∧ ((p4 ∧ (p3 ∨ (p3 → True))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346598346576705731358112561677 : (p3 → ((((True ∨ (p4 → p5)) ∧ (False → (p4 ∧ (p1 ∨ (((((p2 ∧ p5) → p1) → p2) → p1) ∨ False))))) → p5) ∨ (p5 → (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753487567490080902018966239758 : (((False ∧ ((p5 → (((p2 → ((p3 ∧ (False ∨ p1)) → (p2 ∧ (True ∨ False)))) ∧ ((p5 ∨ p2) ∨ p5)) → p5)) → ((False ∧ p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37970726372958302331469660046 : (((((p5 ∨ (((p5 → ((p4 ∧ (p4 ∨ (p5 → True))) → p3)) ∨ p1) → ((p1 ∨ (True ∧ p1)) ∧ True))) → False) ∨ (p4 → p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197960121551241366670754479540 : (((p4 ∧ p4) ∧ ((p4 ∨ True) ∧ (p3 → p4))) ∨ (((p1 ∧ (True → p2)) ∨ p4) → (((((p1 ∧ p4) ∧ p1) ∨ (p5 ∨ p5)) → p4) ∨ True))) := by
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
theorem thm_5_vars_230492446560988524891560714100 : (((True → False) ∧ p5) → (p2 ∨ (((((p5 ∧ True) → (p3 → True)) ∧ p2) → p3) → (True → (True ∧ (False ∧ ((p3 ∨ (True → p2)) ∨ p2))))))) := by
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
theorem thm_5_vars_227474052302627649564587437629 : ((True ∧ (p3 ∧ False)) ∨ (((p5 ∧ (((((((p3 → p2) ∨ p2) ∨ p4) ∧ True) ∧ p4) → p4) ∧ p3)) → (p4 ∧ p3)) ∨ (p4 ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356151176001993587074539186071 : (p5 → ((((((p1 → True) ∧ (p2 ∧ p1)) ∨ (p5 ∨ (p2 ∧ (p4 ∨ p5)))) ∨ p3) → (False ∨ p3)) ∨ ((((False ∨ False) → p3) ∧ False) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40354297716892467576049785009 : (((((((p3 ∧ (True → (p2 ∧ (((False → (p5 ∨ ((True → True) ∧ True))) → False) → p2)))) ∨ (False ∨ p1)) → p2) → p1) ∨ True) ∨ p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306205706627382230064754543578 : (p1 ∨ ((p5 → (p3 ∨ p4)) ∨ (p4 ∨ (((False ∨ p3) → (((False ∨ ((False → p3) ∨ (False → False))) ∧ True) ∨ p3)) → (p3 ∨ (True ∨ False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677296084566408726985400462033 : ((((((p1 ∨ p4) → ((p4 → False) ∨ (p3 ∧ (p3 → (((p2 → p5) → (p3 ∨ p1)) → p1))))) ∧ True) ∨ ((True → (p4 → p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243326226520366479955817450133 : ((p4 → p4) ∧ (True → (True ∧ ((p4 ∨ p4) ∨ ((True ∧ (p4 ∧ (p2 ∨ (((True ∨ False) ∨ p1) ∨ ((False → p2) ∨ p5))))) → (p3 ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300078681051215922011006602481 : (False ∨ ((((True → p3) ∧ (((p1 ∧ (((p1 ∨ (p1 → p3)) ∧ ((p2 ∨ (p5 ∨ False)) ∧ p3)) ∨ p4)) ∨ p3) → p3)) → p3) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68181962873017673136275738178 : ((p3 → (((p5 ∨ (p1 → (((((p1 → p5) ∧ True) → ((p3 → (p2 ∨ (p5 ∨ (p5 ∨ p4)))) ∨ False)) ∧ p1) → p4))) → p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340910044306741669708586631434 : (p2 → (((p4 → (True → ((p2 ∧ ((False ∧ False) ∧ p5)) → False))) → (False ∧ ((p5 → (p5 ∧ (p1 ∨ (p2 ∧ (False ∨ p1))))) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50276709582578398124795188532 : (((((p5 ∨ (p3 ∨ p3)) → ((((True ∧ p4) ∧ (False ∨ (p5 → p5))) → p4) → p1)) ∨ (p3 ∨ True)) ∨ (((p2 ∧ p4) → p2) → p4)) ∨ p2) := by
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
theorem thm_5_vars_4404256420464957548627870622 : (p1 → ((p1 → ((((p2 → ((p4 → True) ∨ (p1 ∨ p2))) → p5) ∧ (p5 ∨ (p2 ∨ (p2 ∧ p2)))) ∨ p1)) ∨ ((p4 ∧ p5) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344116816509710154772882693540 : (p2 → (False ∨ ((p3 ∨ (p5 ∧ ((True ∧ (True ∧ (((p5 ∧ p1) → p1) → (p4 ∧ False)))) ∧ (True → (p4 ∨ (False → True)))))) ∨ (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247459815408453447527194361517 : ((False ∨ p2) ∨ (p4 → ((p2 ∧ p2) ∨ ((p1 ∧ (p3 ∧ (p3 ∨ (False ∧ ((((((p3 ∨ p4) → True) ∨ p4) ∨ p5) ∧ p4) ∨ p2))))) ∨ True)))) := by
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
theorem thm_5_vars_627298565353994931305198452477 : ((((((p3 → (((((True → p5) ∨ (p2 ∨ (((False ∨ (p2 ∧ p5)) ∨ p1) ∧ False))) ∧ p2) ∨ (p3 ∧ p4)) ∨ p1)) ∨ p3) ∧ p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186020072064598706827066154100 : (((p4 → (((True → (False ∧ (p1 → p3))) ∨ True) → p2)) ∧ p4) → ((p2 ∨ p3) ∧ (p4 ∧ (((p1 → (p3 ∨ (p5 ∧ p3))) ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((True → (False ∧ (p1 → p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138437577329340934074680452598 : ((p5 → ((p3 ∨ ((p4 → (p5 ∨ True)) ∧ (p2 ∨ False))) ∨ (False ∨ (p1 ∨ (p3 ∨ (((True ∧ True) ∧ False) ∨ p5)))))) ∨ (p4 ∧ (p4 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164996700149418919988843126231 : ((((p5 ∧ ((((p4 → False) ∨ p2) ∨ p1) → p5)) ∧ ((p1 ∧ (p3 ∨ False)) → p3)) → p4) ∨ ((p5 ∧ p3) → (p1 ∨ ((p1 ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_157041683181388059040615235785 : (((True ∧ (p1 ∧ ((True ∧ p5) ∧ ((((p1 → ((p2 → p2) ∨ False)) ∨ p2) ∨ p5) → p2)))) ∨ p4) ∨ (((p1 ∧ p2) ∨ p1) → (p1 ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310859367421863741885730518002 : (p2 ∨ (((False → True) → False) → ((((True ∧ ((True → ((p2 ∧ p2) ∨ p4)) ∨ (p1 → (((p3 ∧ True) ∨ p5) ∨ True)))) → p5) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653996080655799440081688439015 : (((((p5 ∧ (((p2 ∨ (p4 ∨ False)) ∨ (p2 → ((False ∧ p3) ∧ (p2 ∧ p3)))) ∧ ((p4 → p3) → (p1 ∨ p1)))) ∧ p2) ∨ (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689537702775200258887278194446 : ((((((p3 ∨ (p2 → False)) → ((p1 ∨ p5) ∨ False)) ∨ ((p3 ∧ p4) → (p2 → p2))) ∨ (((True ∧ True) ∨ True) → (True ∨ (p4 → p5)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164874286193425627841398845234 : (((True → ((True ∨ ((p4 ∨ p1) → (p4 ∧ p3))) → (((p3 ∨ p4) ∧ p3) ∧ p4))) ∨ True) ∨ ((True ∨ (True → ((p2 ∨ False) ∨ p5))) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765461807531239090821954886306 : (((p4 ∧ (((False ∨ (((p5 ∨ (p5 ∧ p3)) → ((p5 ∧ p2) ∨ ((p1 ∧ p4) → p1))) ∧ True)) → p2) → (((p5 ∧ p4) → p4) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



