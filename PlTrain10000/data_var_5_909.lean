variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205666318295310594261849328543 : (((p1 ∨ p3) ∨ (p5 ∨ (p2 ∧ p5))) ∨ (True ∨ (True ∧ (((True → (p4 → p2)) ∨ True) ∧ (p2 → (p4 → (p3 → (p5 → (True ∧ p5))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350988906494855885810349740865 : (p4 → ((True ∧ ((False → (True ∧ p2)) ∧ ((p1 ∨ (p3 ∨ True)) ∧ (((p3 → p5) ∨ p1) → ((p2 ∨ (p3 ∨ True)) ∨ False))))) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111091569768126565478527990680 : ((((False ∨ (p3 ∧ ((((p4 → (p1 ∨ p2)) ∧ p1) → p4) ∨ p5))) ∨ ((p1 → p4) ∧ (p4 ∨ (p5 → (p2 → False))))) ∧ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53228037682083988516768430040 : ((((p5 ∨ (p1 → (p4 ∨ p4))) ∨ (p4 → ((p5 ∨ p3) ∨ p4))) ∨ (p3 → ((p4 → ((False → p2) → p4)) ∨ ((False ∧ True) ∨ p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_164689523326126187649214675574 : ((((p4 → (((((p2 → p4) ∧ p1) → p2) ∨ (p4 ∨ p4)) ∨ (p3 → p5))) ∧ p5) ∨ False) ∨ (p3 ∨ (p2 ∨ ((p2 ∨ (p3 → p3)) → True)))) := by
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
theorem thm_5_vars_256363855686320209309983154846 : ((False ∨ p2) → ((p3 → (False ∨ (False ∧ p4))) → (((p5 ∧ ((((p5 ∨ True) → (True ∧ p5)) ∨ (p4 ∨ p4)) ∨ (False ∧ False))) ∨ False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66120995473983459543607363528 : ((p5 ∨ ((True → (((((True ∨ p1) → (p1 → (p3 → (True ∨ True)))) ∨ (p2 ∨ p5)) → (p5 ∨ True)) ∧ ((p1 ∧ p5) → True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114478751942137054191298706897 : ((((p5 ∨ (p1 ∨ (False ∨ (p3 ∧ ((False → p1) ∨ ((p3 ∧ p2) ∨ p1)))))) ∧ (p3 → True)) → (p2 ∨ ((False ∨ p1) → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65385957548691124085644810872 : ((p3 ∨ (((p5 → True) ∧ (p1 ∨ ((p3 → True) → p2))) → ((((p4 ∧ False) ∧ (True ∨ (p2 ∨ p1))) ∨ ((False ∧ p2) → p4)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57941797372468913929195662420 : (((False → (True → p4)) → ((((False → (((p5 ∨ ((True ∨ ((p1 ∧ p3) ∧ p1)) ∧ p3)) ∧ p2) ∨ p3)) ∨ p1) → (False ∨ p3)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48952470959747805302449179554 : ((((p1 ∨ ((p5 ∨ (((False → ((True ∧ p1) → (True ∧ (False ∨ False)))) ∨ (False ∧ p5)) → False)) ∨ p1)) ∧ p4) ∨ (p1 → (True ∨ True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311185925182211786146988137584 : (p2 ∨ ((p1 ∨ p3) → ((p2 ∨ (((p5 ∨ (False → True)) → (False ∧ (p2 → p5))) → (False ∧ True))) ∨ ((p2 ∨ (p4 ∧ p3)) → (p4 → False))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∨ (False → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ (False → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115437699325915277737225139655 : ((((((p4 ∨ p4) ∨ False) ∧ p5) ∧ (p1 → p4)) ∨ (((p3 ∨ (p2 ∧ (p3 → ((False ∨ True) ∧ (p2 ∧ p4))))) ∨ p3) ∨ True)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150332224652023641482477182086 : ((p5 → ((((((p1 → p5) ∧ p3) ∧ False) → (p5 ∧ (p3 → p1))) ∧ (p5 → (p2 → (True ∧ p1)))) ∨ False)) ∨ (((p2 ∧ p1) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321135387134789060858864179274 : (p4 ∨ (p2 ∨ (((((p1 ∨ p4) ∨ (p1 ∨ p5)) → p5) ∨ False) ∨ (p4 ∨ ((((p2 ∨ (((False ∨ p3) ∨ p1) → True)) ∧ p3) ∧ p5) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148392730143185837186015992840 : (((True ∧ (p3 ∨ (p5 → (((False ∨ (p4 ∧ p5)) ∨ (p1 ∧ False)) ∨ p1)))) ∨ (((True ∧ p1) → True) ∨ p5)) ∨ ((p3 ∧ p1) → (p4 ∨ True))) := by
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
theorem thm_5_vars_51940265605829357446086490789 : ((((p5 ∨ ((p3 ∧ ((True ∧ p5) → p4)) ∧ p5)) ∨ (p5 ∨ (p5 ∨ (False → p4)))) ∨ (((p5 ∨ p1) ∨ True) ∧ (p1 ∨ (p5 ∨ p1)))) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115299192068409286778624230962 : ((((((p1 → (True → p3)) ∨ (p4 → p1)) ∧ True) → p1) → ((p3 ∨ False) ∧ ((((False → p2) ∧ p4) → p1) ∨ (False ∧ True)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242148882196204782130394067060 : ((p2 → True) ∧ ((((p2 → ((p1 ∨ p2) ∧ p1)) ∧ p1) → False) ∨ (True ∨ (p1 → ((p2 ∧ (False ∨ False)) ∧ ((p1 ∨ p4) ∨ (p3 ∨ p5))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111569387168521561481522908548 : ((((((p2 ∧ True) ∨ p2) ∨ ((((p1 ∨ p1) ∨ (((p5 ∧ p2) ∨ p2) ∧ p2)) → ((p2 → True) ∧ p5)) ∨ True)) ∧ p1) ∨ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137729183820946210809969379891 : ((p1 ∨ (p5 ∧ (((((p4 ∨ ((False ∧ p4) ∧ p1)) ∨ p4) ∨ (p4 ∧ p1)) ∨ p1) ∨ ((False → (p3 ∨ p3)) ∧ False)))) ∨ (False ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666297604221287954195748463695 : (((((p1 ∨ (((p2 → False) → (((p4 → p4) → (p4 ∨ (p5 ∨ p2))) ∧ (p4 ∧ False))) → False)) → (p2 ∧ p2)) ∧ ((p4 ∨ p3) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158771365128852793420502962311 : ((p4 ∧ (False ∨ (((p5 → ((p3 ∨ (((p1 ∨ p2) ∨ True) ∨ p5)) ∨ (p4 ∨ p1))) ∨ True) ∨ True))) ∨ ((p3 ∧ False) ∨ ((True → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303216710385237666027118752643 : (False ∨ (p4 → (p3 → (p5 → ((False ∧ ((p3 → (((False → p1) ∧ (p3 → p5)) → ((True ∧ p2) ∨ p1))) → (p2 ∨ p2))) ∨ (p5 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193129397611084683976714759555 : ((((p1 ∧ (p4 → False)) → p2) ∨ ((p1 → p3) ∨ p3)) → (((p2 ∨ p4) ∨ True) ∨ ((p3 → ((p2 → (p1 ∧ (True → False))) → p5)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137705143977860942985532481363 : ((p1 ∨ (((p3 ∧ True) ∨ ((((p5 ∨ p4) ∧ p3) → False) → ((True → False) ∧ p3))) → ((p3 ∧ p1) ∨ (p2 ∧ True)))) ∨ (True → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245328890486287301255697590509 : ((p2 ∧ p2) ∨ (p4 ∨ (p3 → (((p5 ∨ (True ∧ (False ∧ (p1 → True)))) ∨ p3) ∨ ((True ∧ (p5 ∨ (((p4 ∧ p1) ∨ True) → p5))) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161294168385702050439847480730 : (((p4 → True) → (p4 ∨ (p5 ∨ ((p3 → (False ∧ (p5 → (p5 ∨ p2)))) ∨ (p1 ∧ (p1 → p1)))))) → (((p2 → p4) → p5) → (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8977045762915147286994892855 : (((((((((p4 ∨ p1) ∧ p3) ∧ p5) → (p5 → p3)) ∧ (True ∨ p1)) → (p5 ∨ p4)) ∨ (p2 ∨ (False → (p3 → (p3 ∨ p4))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721815010299771519105430471729 : ((((p3 ∨ ((p5 → p1) ∧ False)) → (False ∧ ((((((False → p5) ∧ (p1 ∨ False)) ∧ p2) ∨ ((p3 ∨ p2) ∨ (p2 ∨ p1))) ∧ p5) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62740630932654566877954353210 : ((p4 ∧ (((p1 ∨ (p3 ∨ (p2 ∧ (p4 ∨ p4)))) ∨ (((p5 ∨ ((p4 → p1) → p4)) ∨ p1) ∧ ((p3 ∨ p1) → False))) ∨ (p1 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346373437614935778928769904606 : (p3 → ((p4 ∧ (((p3 ∧ (p4 → p2)) ∧ (((p1 ∨ (p2 ∨ False)) ∨ p1) ∧ (p2 ∨ p5))) ∧ (p5 ∨ (p1 ∨ (True ∨ p5))))) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174260648182469421746380019315 : ((((p1 ∧ (((p4 ∨ (p1 ∧ p5)) ∨ p1) ∧ p2)) ∨ p4) ∧ ((p3 → p5) ∨ p1)) → (((p5 → (False ∧ True)) ∨ True) ∨ (p1 ∨ (False ∧ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320495854802525874859094026842 : (p4 ∨ ((p5 → p5) → (True → (p3 → ((True ∧ ((((p2 ∧ True) ∨ p1) ∨ (p3 → (p4 ∧ p3))) ∨ False)) ∨ (((p4 ∧ p3) ∨ True) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164704120182466556512861086367 : (((((p1 → p1) ∧ (p3 → ((False ∨ False) ∧ (((True → p1) ∧ p4) ∨ True)))) ∨ p3) ∨ p5) ∨ ((p5 ∧ (p4 ∧ p1)) ∨ ((p4 ∧ False) → p5))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325673560021072850809006095499 : (p5 ∨ (p1 ∨ ((((((((p1 ∨ ((p4 → p3) ∧ p3)) ∧ p1) → (p4 → p4)) ∨ True) ∨ p5) ∨ True) → (p1 ∨ ((p3 ∧ False) → p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4228504905856835757310045536 : (p5 ∨ (((p5 ∨ (p2 ∧ False)) ∨ (((p3 → True) ∧ (False ∨ False)) ∧ p2)) ∨ (True ∧ ((False ∨ (((False ∧ p4) ∧ p1) → p1)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692228065398811723353887751814 : ((((((p5 → p5) ∧ (((True → ((p5 → True) ∨ p1)) → p5) ∨ p4)) ∨ True) ∧ (True ∨ ((p1 → (p3 → False)) ∧ ((p1 ∨ p4) ∨ False)))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636352897034585310701684594591 : ((((((((False ∧ (False ∧ (p2 ∨ p5))) → p3) → p5) ∧ (p3 ∧ ((p2 ∧ False) ∨ False))) → (((p2 ∨ (p4 → p1)) → False) → p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748913623668991122950740291474 : ((((p4 → p2) → (((True ∨ p5) ∧ (p1 → p5)) → ((p1 ∨ ((p1 ∨ True) → p5)) ∨ (p2 → ((p2 → ((p2 ∧ True) ∧ True)) ∨ False))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158012626384172963969007057436 : ((((p5 ∨ ((p2 ∨ p2) ∨ False)) ∨ p2) ∧ (True → (True → (p3 ∨ (((p1 ∧ False) ∨ p5) ∧ p5))))) ∨ ((p5 ∧ (p1 ∨ p1)) → (True ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133998008392626591289602663277 : ((((((True ∨ False) ∨ (True ∧ p2)) → (p1 ∨ ((p4 ∧ p5) ∨ ((True → p4) → (p5 ∧ (p3 ∨ True)))))) ∧ True) ∨ p3) ∨ (True ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258784996970371585536731373059 : ((True → False) → (((((p3 → p4) ∨ p5) → (p2 → p5)) → (p5 ∧ (p5 ∨ (p3 ∧ p4)))) ∨ (p3 ∧ ((p1 ∨ ((False → p3) ∨ p2)) ∨ True)))) := by
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
theorem thm_5_vars_349878962234444378052322038339 : (p4 → ((p3 ∨ ((((p1 ∨ p2) → ((False ∧ ((p1 ∨ (p5 ∧ p1)) ∧ p1)) ∨ (False ∧ (((p5 → True) → p5) ∧ p3)))) ∧ False) ∨ p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319744468638726037510401551390 : (p4 ∨ (((p1 ∧ (True ∧ p4)) ∨ (p5 ∨ p3)) ∨ (p5 ∨ ((((False ∧ ((p2 ∨ (p4 ∨ p4)) ∧ (p2 → p4))) ∨ p3) → p1) ∨ (p5 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119432171473268572985356419843 : ((p4 → (((p1 ∨ (p2 ∨ p5)) ∧ ((p4 ∨ (True → p2)) ∧ ((p3 ∧ ((p3 ∧ p4) ∨ p1)) → p1))) ∨ (p5 ∨ (True → p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111977529985111535994702016746 : (((((p3 ∨ p4) → (p3 ∨ (p1 ∨ p1))) ∨ ((True → (p5 ∧ (((p5 ∧ True) ∧ p4) ∧ ((p5 → p4) ∧ p1)))) ∨ True)) ∨ p3) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47965190851386886262801846650 : (((((((False → p2) ∧ (p1 ∨ p3)) ∧ True) → ((((p3 ∧ p5) → True) ∨ False) ∨ p2)) ∧ ((p1 ∧ (False → p2)) → p4)) → (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637107392182315472327652688687 : ((((((False ∧ ((p3 ∧ (p2 → p5)) → ((False ∧ p2) ∧ False))) → p4) ∨ (((True ∨ ((p5 → (p2 ∨ p2)) → True)) ∧ p3) ∧ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673389672890913035836803794140 : (((((((p4 → p5) → (True ∧ True)) ∨ p2) → (((False ∨ (p5 ∨ p4)) → ((p4 ∧ (p3 ∨ p1)) ∨ p2)) ∧ False)) → (False ∧ (p2 ∧ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → p5) → (True ∧ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 → p5) → (True ∧ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p4 → p5) → (True ∧ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42508292033732383775657233325 : (((False ∨ ((p3 → ((True → False) ∨ p5)) ∧ ((p2 ∨ (False ∨ (((p3 ∧ False) ∧ p3) ∨ p2))) ∨ (((False ∨ p4) ∨ p2) → True)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300681926955029464928298810854 : (False ∨ (((p5 ∨ (p5 ∧ (True ∨ True))) ∧ (p3 → (((p3 → (p3 ∨ p4)) ∧ (p4 ∧ p2)) ∨ p2))) ∨ ((p3 → (p5 ∨ p2)) → (p1 → True)))) := by
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
theorem thm_5_vars_616962501054303765051851929657 : (((((p1 → (p5 → (p1 → (p4 ∧ ((p1 ∧ False) → True))))) → (((False ∧ (p4 ∧ p5)) ∨ p5) ∨ ((p2 ∨ p4) ∨ (p1 → p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654367942821535151950815790352 : (((((((((p4 → (True ∧ p2)) ∨ p4) ∨ (p1 → p5)) ∨ True) → ((p3 → p4) ∧ (p1 → (p4 → (p2 → True))))) ∨ True) ∨ (p1 ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791888511605414095217052400560 : (((True → (((((((p2 ∨ (p4 ∧ p3)) ∧ p3) → ((p1 → (False ∨ ((p3 → p5) ∧ p4))) → p2)) ∨ p3) ∨ p4) ∧ p3) ∨ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114151781589324191120688821114 : (((((p2 ∧ (p2 ∧ True)) → ((True ∧ (p3 → (False → ((False ∨ p1) ∧ p5)))) → (p3 ∨ p4))) ∨ False) → (p4 → (p1 → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207396638524159820928284327809 : (((p2 ∧ (p4 → (True ∧ p1))) ∨ p2) → ((((p2 → (p2 ∧ False)) ∧ p4) ∨ p5) ∨ ((p4 ∧ True) ∨ (p4 ∨ (p2 ∧ (p5 ∨ (p4 ∨ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345736478261641106431993133865 : (p3 → ((p5 → (p3 → ((((p3 → ((p3 → True) → (p5 → (False ∨ ((False ∨ (p1 ∨ True)) ∧ (p2 ∧ False)))))) → p2) → p1) ∨ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56889150947201811679702057237 : (((p3 ∧ (p3 ∧ True)) ∧ (((((p2 ∧ p4) ∨ False) → p5) ∧ (((p2 ∨ ((p5 ∨ True) ∧ p2)) ∨ ((p2 → p4) ∨ p3)) ∧ p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178301121422592633052231989947 : (((p5 → (((True ∨ (True ∨ p4)) ∨ (p5 → True)) ∨ p5)) ∧ (False ∧ p4)) ∨ ((((True → True) ∧ p1) ∧ ((p3 ∧ (p5 ∧ p4)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64104247452824352092931293232 : ((False ∨ (((p1 → p1) ∧ (p4 ∨ (p2 → (False ∨ p2)))) ∧ (p1 ∨ ((((p2 → (p1 ∧ p2)) ∧ p3) ∨ True) ∨ (p2 → (p3 ∨ False)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51748791304422008656913403154 : ((((p1 ∧ p1) ∧ (((((p4 ∧ p4) → p1) ∨ p5) → (p5 → p2)) ∨ (False ∧ True))) ∧ ((p4 ∧ p1) ∨ ((p3 ∧ (p2 → p3)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180246272675847383429097294939 : (((True ∨ (((p2 ∧ p2) → p4) ∨ (p1 → (False → (p2 ∧ p2))))) → False) → ((((((p1 → p5) ∧ p2) ∨ (False → p1)) → False) ∧ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p2 ∧ p2) → p4) ∨ (p1 → (False → (p2 ∧ p2))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47354191940410210948059468284 : ((((p1 ∧ p4) ∨ (((False ∧ p4) → (p5 → ((p5 → (p5 ∨ False)) → ((p4 → p5) ∧ (True ∨ p5))))) ∧ (p5 ∧ p2))) ∨ (p1 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185281111946175260633921734366 : ((p2 ∧ ((p4 ∧ ((((p2 ∨ p2) ∨ p4) ∧ p3) ∧ p1)) ∨ p4)) ∨ (True → (((p5 → (p5 → (p2 ∨ False))) → p3) ∨ (True ∧ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193875069978564431308635093934 : ((False ∨ ((True → (True → ((p5 → p2) ∧ p1))) ∨ p2)) → ((p3 ∨ p2) ∨ ((p5 ∨ (((p4 → p4) ∨ p4) ∧ (True ∨ (p4 ∨ p1)))) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150290692579664283574563435256 : ((p4 → ((((True ∨ p2) → p5) ∨ (((True → (p4 → (p4 ∧ p1))) → (True ∨ p5)) → (p3 → p1))) → False)) ∨ (True ∨ (p5 ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259494434411172753335376491616 : ((False → p5) → ((((p3 ∧ p1) ∨ p1) ∨ (((((p4 → (p4 ∧ True)) ∨ p5) → (False ∧ (True ∨ (p5 ∧ p3)))) ∧ False) ∨ (True → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48558498325656808010670810018 : (((((((True ∧ (True → (((p2 → p2) ∧ p5) ∨ False))) ∨ p5) → p1) ∧ (p2 ∨ (p2 ∨ (True ∨ False)))) → p5) ∧ (p5 ∧ (True ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117800345388639784574679910417 : ((p4 ∧ (((p2 ∨ (p4 ∨ p4)) ∧ p3) ∧ ((((((p4 ∧ ((False → p4) ∧ True)) ∨ p2) → True) ∨ p4) ∨ False) → (p5 → True)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114962113345723576393975980079 : (((p4 ∨ ((((False ∨ False) → p4) → (((False ∨ p4) ∨ p1) ∨ p3)) → p4)) → (((True ∨ (p3 → (False ∨ p2))) ∧ False) ∨ False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218083032760452679705131409305 : (((True → True) ∧ (p1 ∨ p1)) → ((((p3 → (p5 ∧ p2)) ∧ ((p5 → (((True → p5) → ((True → p2) → p3)) → p3)) ∨ True)) → p4) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586939754853316819595611985609 : (((((p2 ∨ ((((p2 ∧ p2) ∧ (p5 ∧ ((p5 ∧ (p3 → p3)) → p5))) → (((p4 ∧ p5) ∨ p1) ∧ p1)) → (False ∧ p5))) ∧ True) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136276690200726735475183179402 : ((((p4 ∧ (p5 ∨ p3)) ∨ (False ∧ p4)) → ((p2 ∧ (p5 → (p5 ∨ (((p5 → (True ∧ p5)) ∨ p4) ∨ p2)))) ∨ False)) ∨ (True ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726972782063570774084042424140 : (((((False → p5) → False) ∨ ((((p5 ∨ (p3 ∨ False)) ∨ (True ∨ p2)) ∨ (p4 → (p3 → ((True ∨ False) ∧ ((True ∧ p4) ∧ p3))))) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117338768552367679932476718521 : ((False ∧ ((p3 ∨ p1) ∧ (p5 ∧ (((((((p4 ∨ False) ∨ (p2 ∧ p5)) → p5) ∧ ((True ∧ False) ∨ p1)) → False) ∨ False) ∧ p2)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175336433126212869107040920637 : ((p4 ∨ (p5 → ((((p4 ∨ (p1 ∨ p3)) → False) ∧ (p2 → (p5 → True))) ∨ p2))) → (p1 ∨ ((((p1 ∧ p5) → p2) ∧ (p1 ∨ p1)) ∨ True))) := by
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
theorem thm_5_vars_740067622377900462457899883768 : ((((False ∨ p1) ∨ (p2 ∨ ((((((p1 ∧ p1) ∨ p1) → (p3 ∧ p1)) → (p3 ∧ (p1 ∧ p2))) ∨ ((p1 ∨ p1) ∨ (True ∨ p3))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44793267510089276370723166433 : (((((p3 ∧ p4) ∨ p5) ∧ ((p1 → p4) ∨ (p4 → (True → ((False ∧ (((p4 → p2) ∨ p1) ∧ ((p4 ∨ False) ∨ p5))) ∧ p3))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48332836939897832962876731656 : (((p2 ∨ (((((p3 ∨ (True ∨ p4)) → (False → False)) → ((p2 → ((p1 → p5) → p2)) ∨ (p5 → p3))) ∧ p2) ∨ p3)) → (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316371204931208354464295702376 : (p3 ∨ (False ∨ ((((((p5 ∧ p1) ∧ (((((True ∧ p1) ∨ True) ∨ (False ∧ False)) ∨ p3) ∧ p5)) ∧ False) ∨ (p3 ∨ (False ∨ True))) → p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∧ p1) ∧ (((((True ∧ p1) ∨ True) ∨ (False ∧ False)) ∨ p3) ∧ p5)) ∧ False) ∨ (p3 ∨ (False ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330503057982368803413735869729 : (True → (p4 ∨ (((p5 ∧ ((p5 ∧ True) ∨ p2)) ∨ (p1 ∨ p3)) ∨ (p3 → ((((p1 ∧ (p1 → p3)) → p4) ∧ p4) ∨ ((p1 → p2) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_140702927157342496049252365706 : ((((((p5 → False) ∨ p4) ∨ (True ∧ True)) ∨ (p2 → ((p5 → p2) ∧ p3))) ∨ (True → ((p5 ∧ p3) → (p1 ∨ p1)))) → ((p2 → p1) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355668924093407703941946266025 : (p5 → (((((p2 → p4) → ((False → (((True → False) → (p5 ∧ p4)) ∧ ((p2 ∨ (p3 → True)) ∨ False))) ∧ p4)) → p1) → p3) → (p1 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → p4) → ((False → (((True → False) → (p5 ∧ p4)) ∧ ((p2 ∨ (p3 → True)) ∨ False))) ∧ p4)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313127614354776225325499204159 : (p3 ∨ ((((p4 ∧ p5) → (((True ∨ (True ∧ True)) ∧ ((p4 ∧ False) ∨ p4)) → (False ∨ (p2 → p3)))) ∨ (p5 → ((p5 → p4) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221572800289325204928108267416 : (((p3 → p3) ∨ p4) ∧ (((((p2 ∧ p3) ∨ False) ∧ (p4 ∧ p1)) ∧ (((p2 → p4) ∧ (((p5 ∨ True) ∧ p4) → p3)) ∧ (p5 → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66136824128009890788701538711 : ((p5 ∨ ((((False → ((False ∧ (p2 → ((p2 ∧ (False ∨ p4)) ∨ (p1 → p5)))) ∧ ((p5 ∧ True) → False))) → p3) ∨ True) ∨ (p4 → p1))) ∨ p4) := by
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
theorem thm_5_vars_68955896301925640888872827794 : ((p4 → (p1 → ((p4 → ((((p4 → (((True ∧ (p2 ∨ p4)) ∧ p3) ∧ ((False ∨ True) ∧ p3))) ∨ p3) ∧ p2) ∨ False)) ∨ (False ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124136170546582092578675166957 : (((p5 ∧ (p5 ∧ (p4 ∨ (p4 ∨ ((True ∧ p1) → p3))))) ∧ (p3 ∧ ((True → p1) ∧ (p3 → ((True ∨ (p4 ∨ p5)) ∧ p2))))) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h29 := h26 h28
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314434458882055882756922187489 : (p3 ∨ ((False ∧ (p4 → ((((p1 ∨ True) → p5) ∧ ((p1 ∨ ((p5 ∨ (p5 → True)) → p4)) ∧ p2)) ∧ False))) ∨ ((p4 ∧ p1) ∨ (False → p4)))) := by
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
theorem thm_5_vars_112110680468720973591356969864 : ((((True → p1) → (((((p5 ∨ p5) ∧ p1) ∧ (p2 ∧ (p4 ∨ (p2 ∨ p3)))) ∧ (p4 ∨ p2)) ∧ (p1 ∨ (p2 ∧ p1)))) ∨ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40928734090183592442928279346 : (((((((p1 ∧ ((p4 ∨ True) ∨ ((False ∨ p1) ∧ p5))) ∨ p3) ∧ ((p4 ∨ ((p5 ∨ p4) → True)) ∧ p4)) ∧ False) ∨ (p3 → True)) ∨ p1) ∨ p1) := by
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
theorem thm_5_vars_238330377178989755022446768161 : ((False ∨ True) ∧ ((True ∨ False) ∧ (((p3 → (((p4 ∧ p4) ∨ p1) ∨ p3)) → ((p1 → (p3 ∨ False)) ∨ True)) ∨ ((p3 ∨ (True ∨ False)) ∧ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219140163807194674639355731488 : ((True ∨ (p5 ∨ (p3 → True))) → ((p3 → p4) ∨ ((p1 → ((p4 ∧ (True → (p3 ∧ p1))) ∧ (p1 → p1))) ∨ ((p5 → p1) → (p5 → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157859741718595998853845954353 : (((p5 ∧ ((((p4 ∧ True) → (True ∧ p5)) → p5) ∧ p2)) ∧ (p2 ∧ (p1 ∧ (p4 ∨ (p5 ∨ p4))))) ∨ ((p1 ∨ (False → (p2 ∧ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_743061508209143341261149879598 : ((((p4 → False) ∨ (True → ((p5 ∨ (True ∨ (p4 ∧ p1))) → ((p4 → ((False ∧ p3) ∧ p2)) → ((True ∨ (p3 → p5)) → (p3 ∨ True)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h13 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310296557593806004352320074844 : (p2 ∨ (((p3 ∨ ((((p4 ∧ p5) ∨ p3) ∨ False) ∨ p1)) → p5) ∨ (((True ∨ p5) ∧ (False ∨ p4)) ∨ (p4 ∨ ((p1 ∨ p1) ∨ (p1 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249413936690883952459347154945 : ((p5 ∨ False) ∨ ((True ∧ ((((p2 ∨ ((((p4 → p3) → (p5 ∧ p5)) ∨ p2) ∨ True)) → False) ∧ True) → ((p5 ∨ (p1 ∨ p1)) ∨ p2))) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ ((((p4 → p3) → (p5 ∧ p5)) ∨ p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355641025569814298419525087149 : (p5 → ((p4 → ((True ∧ ((((p3 ∨ (True ∨ (p2 → p3))) ∧ True) ∧ (((p1 ∨ p2) → p3) → False)) → (True → p1))) ∧ True)) ∨ (p2 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49979677523819271264086888621 : (((((p4 → ((p4 ∨ ((p3 → p4) ∧ p5)) ∨ p1)) → (p2 → False)) ∧ (False ∧ ((True ∧ False) → p4))) ∧ ((p1 ∨ (True → p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



