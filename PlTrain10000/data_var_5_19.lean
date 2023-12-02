variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41806388636644491531637790804 : ((((p2 → ((p5 → p2) ∨ False)) → (((p5 ∨ ((((p4 → p4) ∨ True) ∧ ((True ∨ p3) ∧ (p2 ∧ False))) ∨ p5)) ∧ False) ∨ p5)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758447975092833728468347019809 : (((p2 ∧ (((p2 → p5) → (((p3 ∨ (False ∧ (((p4 ∧ (True ∨ p1)) ∧ ((p3 → True) → False)) → False))) ∧ (p5 ∧ p4)) → p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165912480901214685712681754146 : (((p5 → (p4 ∧ p3)) → (p3 ∧ ((p5 ∨ p2) ∨ (((p1 ∨ p3) ∧ (p3 ∨ True)) → False)))) ∨ (False ∨ (p5 → (((p3 → p5) ∨ True) → p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49274330110062208531662759781 : (((p3 ∧ ((((True ∧ p4) ∨ (p5 ∧ ((p3 → (p2 → p5)) → p1))) → ((True ∨ p3) ∧ (p3 ∨ p5))) → p5)) ∨ (True ∨ (False ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767673166132773195092976283812 : (((p5 ∧ ((p4 ∧ (p5 ∧ ((p1 → (True ∧ (p2 ∨ ((p5 ∧ (((p1 ∧ False) ∧ (p1 → p1)) ∧ False)) → p2)))) ∨ (True ∨ p2)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232052439240829061619551426167 : (((p3 ∨ p5) → p1) → (False ∨ ((p1 ∧ (((True → p2) → p3) ∧ p3)) ∨ ((p1 ∨ (p2 ∨ (p5 ∨ (p4 → True)))) ∨ (False ∨ (False → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315256727415713084511022353312 : (p3 ∨ ((p1 ∧ ((p2 → p3) ∧ p2)) ∨ ((p4 → (((p2 ∧ p3) ∨ (p3 → (p1 ∨ True))) ∨ p1)) ∨ ((p4 ∧ ((p5 → p2) ∧ True)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157247281880913582436321908818 : (((((True ∨ True) ∨ (p4 ∨ (p2 ∨ p2))) ∧ ((p5 ∧ (p1 ∨ (p3 ∧ p1))) ∧ (True ∧ p1))) → p3) ∨ (False ∨ (True ∨ (p1 ∧ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135279251550492061800173736774 : (((True → ((p5 ∧ (((((p5 → (p4 → (p2 → p2))) ∧ p3) → True) → True) ∨ p2)) ∨ (p5 ∨ p5))) → (p4 ∧ p2)) ∨ (True ∨ (p1 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50757104887917987271257995591 : (((p5 ∧ (((p5 → ((False ∧ True) ∧ ((p2 → p2) → (p2 ∧ p3)))) → (False ∧ (False ∨ p1))) → False)) → ((p2 ∧ p5) → (False ∧ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 → ((False ∧ True) ∧ ((p2 → p2) → (p2 ∧ p3)))) → (False ∧ (False ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h17 := h6 h7
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h22 : ((p5 → ((False ∧ True) ∧ ((p2 → p2) → (p2 ∧ p3)))) → (False ∧ (False ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- False on the left can always be used.
    apply False.elim h27
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h28 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h29 := h23 h28
    -- We need to get the left conjuct of h29 based on <expert-advice>.
    let h30 := h29.left
    -- We need to get the left conjuct of h30 based on <expert-advice>.
    let h31 := h30.left
    -- False on the left can always be used.
    apply False.elim h31
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h32 := h21 h22
  -- False on the left can always be used.
  apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226372914789825330455485204282 : (((True → p3) ∨ p1) ∨ (((p1 ∨ p3) → p1) ∨ ((p3 ∧ (p3 → (p5 ∧ p3))) → (((p1 ∧ ((p1 ∨ p2) → p4)) ∨ p5) ∨ (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760426635453820795538111691 : (((p4 → (p1 → True)) → ((p5 ∨ (p5 ∧ (((((True → p5) → (p1 → p1)) ∨ False) ∨ False) ∨ ((False ∧ p5) → p1)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115561573973028266493636098162 : (((((p4 → (p4 → True)) → p5) ∨ p4) ∧ ((p5 → p2) ∨ (p4 → ((p1 → p1) → (p1 ∨ (p4 → (p2 → (False → True)))))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315670821906536495495552552026 : (p3 ∨ ((p5 ∧ True) ∨ (((p1 ∨ ((p1 → p1) → (False → p4))) ∧ ((p3 ∨ p3) ∧ p1)) ∨ ((p4 ∨ (p5 → True)) → ((False → p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_42294023873775796453055771205 : (((p2 ∧ ((((p2 → p2) → (((p4 ∨ (p3 ∨ p2)) ∧ p2) ∧ ((p2 → False) → (p4 ∧ p1)))) ∨ ((p4 → p4) ∨ p5)) ∨ p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755619614305643610114026956759 : (((p1 ∧ ((((p5 → p1) ∨ (((p4 ∧ (p4 ∨ p3)) ∨ (p3 ∨ ((p2 → (p3 ∨ p4)) ∧ p4))) → (p2 ∨ (True ∨ p4)))) → p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677803803725299527168777174682 : ((((((p2 ∨ (((p5 → False) ∨ ((p2 → (True ∧ p3)) → p1)) ∨ (p1 ∨ p1))) ∧ False) ∧ (True ∨ p4)) ∨ (p1 → ((p5 ∨ True) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165429945653367784187698644174 : ((((p2 ∨ True) → (p2 ∨ (((True ∨ p2) ∧ p1) → (False ∧ False)))) → (p2 ∨ (p5 ∨ p4))) ∨ (p1 → ((p1 ∨ (True ∧ (p1 → p3))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133693063245967410168231466724 : ((((((p3 ∧ True) → (((p2 ∧ p4) → p2) ∨ (p3 ∧ (p5 ∧ (p4 ∧ False))))) ∧ p3) → ((p2 ∨ True) → p4)) ∧ p4) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213102162556639896382515200008 : ((((p1 ∨ p1) ∧ p4) ∧ p2) ∨ ((((p1 ∨ ((p3 ∧ False) → p3)) → ((p4 ∧ p4) → p5)) ∨ ((False ∧ True) → p2)) ∨ (p5 → (p2 ∨ p4)))) := by
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
theorem thm_5_vars_187793033114239070154542155022 : ((p3 → ((p4 ∧ False) → (True ∨ (p2 → ((p1 → p2) ∧ p4))))) → (((p4 ∧ True) ∧ ((p4 ∨ ((p3 ∧ p1) ∨ p2)) → p5)) → (p5 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ ((p3 ∧ p1) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809978188723639057602220787935 : (((p5 → ((p3 ∨ ((True ∨ (False → p5)) → ((((p4 ∨ (p3 ∧ p3)) → False) ∨ p1) ∧ (p1 → (False → p2))))) ∨ (p2 ∧ (False ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753423686511224291734393738817 : (((False ∧ (((False → (p5 → ((p4 → p5) ∧ p2))) ∧ (False ∧ (True → (((p1 ∧ False) ∨ p1) ∨ (p2 ∨ False))))) ∨ (p5 ∨ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208844846470339593875180277259 : ((p3 ∧ (p2 → ((p1 ∧ True) ∧ p1))) → (((((p4 ∨ p4) ∧ p4) → p2) ∨ False) → ((p3 → (p2 → (p5 ∨ True))) ∧ (p1 ∨ (True → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46678458605682143311312449787 : (((p1 ∨ (p5 → (((True → (((((p5 ∧ p2) → (False ∨ p2)) ∧ p4) ∨ p3) ∨ p2)) ∨ p2) ∨ (False → (False ∧ True))))) ∧ (True ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229958506017021367263465722758 : (((True ∧ p4) ∧ True) → ((True → ((True → (p5 ∧ p3)) ∨ (((p2 → ((((p3 → True) ∨ (p3 ∧ False)) ∨ p3) ∧ p4)) ∧ p1) → p2))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114659914861028549253631075968 : ((((p5 ∨ ((p3 ∧ False) ∨ p5)) ∨ (p4 ∨ (p5 ∨ (((p5 ∨ True) → p1) → p3)))) ∨ (p1 ∨ ((p1 → p5) ∨ (p5 ∧ p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118722553699747055339562343579 : ((p5 ∨ ((p3 → ((p3 ∧ (p4 → (True ∧ p5))) ∧ (((p1 ∨ True) → (p5 ∨ (p1 ∨ p4))) → False))) ∧ ((False ∨ p1) ∧ p3))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260161764333057843040017313210 : ((p2 → p2) → ((((p1 → ((True ∧ True) ∧ (p4 → (p3 ∨ p4)))) ∨ p5) ∧ (p1 → ((False ∧ (p2 ∧ ((p3 ∨ p3) ∨ p4))) ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340754497515929360282017854752 : (p2 → ((((p5 ∧ p4) ∨ (((((p5 ∧ (p3 → (p4 ∨ p3))) → ((p5 ∨ (p1 ∧ p2)) ∧ (False → p1))) ∧ p5) → p1) ∧ p1)) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709002831617300507220822517153 : (((((True → ((p2 ∨ p3) → True)) → (p3 → p1)) → ((p4 ∨ ((p1 ∧ p2) ∨ (True ∨ ((False ∧ (p4 ∨ p3)) → (p1 → p3))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330358173120179672336376598459 : (True → (p2 ∨ ((((False ∧ (p2 ∧ False)) ∨ False) ∨ ((p3 ∨ p5) → (p1 → (p5 ∨ ((p2 → (p5 → ((p4 → False) ∨ p2))) ∨ p4))))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348761857595044917507224220044 : (p3 → (False ∨ ((True → p4) ∨ (((p4 ∨ False) ∧ (((p5 ∨ ((p3 ∧ False) ∧ p2)) ∧ p2) → ((((p1 ∨ p1) ∧ False) ∨ p1) ∨ p5))) → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254818135736998438646416349379 : ((p3 ∧ p5) → (((p3 ∨ ((p5 ∨ p2) → p5)) → (p3 → (p2 ∧ (p4 → ((p5 ∧ False) ∧ (((p2 ∧ (p4 ∨ p2)) → p4) → p5)))))) ∨ p5)) := by
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
theorem thm_5_vars_201234725504650344378783784079 : ((p2 → (p1 ∨ (((p1 ∨ p3) ∨ p1) ∨ False))) → (True → (p4 → ((True → ((p5 → (p2 ∧ (True → p4))) → (p2 ∨ p3))) ∨ (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54966626709157521902361997872 : (((((True ∨ p1) ∨ p3) → (False ∧ p5)) ∧ ((True ∧ (((p1 ∨ p4) → True) → (p1 ∨ p1))) → ((p5 ∨ False) ∧ (p1 ∧ (p4 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205396546118391076623227010614 : ((((False ∨ p1) → True) → (p3 ∧ p3)) ∨ ((((((p2 → (p2 → p5)) → p5) ∨ (p3 → True)) ∨ (p1 ∧ p4)) ∧ (p1 → (p1 ∨ p3))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59169009411313063583979694337 : (((False ∨ p3) ∨ (p2 ∨ (((((p4 ∨ False) ∧ p5) → p1) → ((p3 ∧ (False ∧ True)) ∨ (False → True))) ∨ ((p3 → p5) → (True ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58767903955023837441511568407 : (((p4 → p2) ∧ ((p3 → (((p1 → (True → p2)) ∨ p2) → p2)) ∨ (((p4 → ((p2 ∨ ((p1 → p2) ∨ p5)) ∧ False)) ∧ p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57760922958576596425448773698 : ((((p3 → p5) → True) → ((p4 → False) ∧ ((p4 ∧ (((p3 ∧ (False ∨ (p1 ∨ (p1 ∨ (p4 ∨ p5))))) ∧ (False ∨ p3)) ∨ True)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937330029047853369053704241096 : (((((True ∧ p4) ∧ (True ∧ (True ∨ p3))) ∧ (((p1 ∨ True) → False) ∧ (p4 ∧ (p3 ∨ ((((p5 ∧ p3) ∧ True) ∧ p3) ∧ (p1 → p5)))))) → p2) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h17 := h11 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h27 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h28 := h11 h27
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h35 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h36 := h30 h35
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h38.left
      let h41 := h38.right
      -- Conjunctions on the left can always be decomposed.
      let h42 := h40.left
      let h43 := h40.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h42.left
      let h45 := h42.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h46 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h47 := h30 h46
      -- False on the left can always be used.
      apply False.elim h47
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46542027497968937119148328050 : ((((p1 → p3) ∨ (((p3 ∧ p3) → p2) → ((p2 ∨ (p5 → ((p3 ∨ ((p4 ∧ p3) ∧ p5)) ∨ p2))) → (p2 ∨ p2)))) ∧ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801183739790311439464454607125 : (((p2 → (((p1 ∧ p2) → ((((p5 ∧ (((False ∧ p5) ∨ p2) ∧ (p2 → p3))) ∧ p3) → p5) ∧ p5)) → ((True ∨ p5) ∧ (p3 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349958635861191161680033748070 : (p4 → ((((p3 → (True ∨ p1)) ∧ ((p2 → p1) ∨ (((True ∨ (p3 ∧ True)) ∧ ((p4 → (True → True)) ∧ p5)) ∧ (p5 ∨ p3)))) ∧ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300567670661498855633437463053 : (False ∨ ((p4 ∧ ((p1 → False) ∨ ((((p1 ∧ ((p3 → True) ∧ (p4 ∨ p5))) → p1) → p1) ∧ (p3 → True)))) ∨ (p3 ∨ (True ∨ (p3 ∧ p1))))) := by
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
theorem thm_5_vars_621527608271827841710492442174 : ((((False ∧ (((((p2 ∧ (p2 ∧ p4)) ∧ p3) → ((p3 → p4) ∨ (((p2 ∨ False) ∧ p4) → (p1 ∨ p3)))) ∨ True) → (p3 ∨ p1))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149477997412652348514470570117 : ((False ∧ (p2 ∨ ((p5 ∧ (True → (p4 → (p2 ∧ (((p3 ∨ (False ∧ True)) ∨ (p4 → p2)) → False))))) ∨ p5))) ∨ (p3 ∨ ((p5 ∨ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158662286796913388320203809054 : ((p1 ∧ (True → (((((p3 → ((p2 ∨ False) → False)) ∧ p1) ∧ p4) ∨ (False ∧ (p2 ∧ p5))) ∧ False))) ∨ (p2 → (p2 → ((p2 ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161381616656201971453231504680 : ((p1 ∧ (((p5 → p3) ∧ (p5 → (((p3 ∨ (((p1 ∧ p1) ∨ p1) ∧ p4)) ∨ False) → True))) ∨ p1)) → ((((p4 ∧ p3) ∧ p1) ∨ p1) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354585968426574048834773251623 : (p5 → ((((p4 → p5) → ((((p2 → p5) ∧ ((p2 ∨ p1) → ((True ∨ True) → p2))) → p5) → (((True → p5) ∨ True) ∧ False))) ∧ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149483128961173931608216154975 : ((False ∧ (p3 → ((((p3 → p2) → (False ∧ True)) → (((p3 ∨ True) ∧ (p3 ∧ (p2 → p1))) → p2)) → p4))) ∨ (p1 → ((p1 ∨ p4) → p1))) := by
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
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51963134198122618480045384840 : (((((p5 ∧ p2) ∧ p3) ∧ (p1 ∨ ((p3 ∨ (True ∨ ((p5 ∨ p5) ∧ p2))) ∨ p3))) ∨ (((p1 ∧ (p4 → True)) ∨ False) → (p2 → p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335760598779999465280924995288 : (p1 → ((((((((p2 → True) ∧ True) → (True ∨ False)) → (p1 → (((p5 → (p3 → p2)) ∨ p2) ∧ False))) ∧ p1) → p3) ∧ (p2 ∨ p1)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p2 → True) ∧ True) → (True ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59482306049251060885884710904 : (((p1 → p3) ∨ (((False ∨ (p3 ∧ p1)) ∧ p4) ∨ (((((p5 → p4) ∧ p1) ∧ ((p4 ∧ True) → (True ∨ True))) → (p3 ∨ False)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53587266503975390086076123500 : (((((True ∨ ((p3 ∨ p1) → p3)) ∨ (p5 ∨ p1)) → p2) ∧ (((p3 → p4) ∧ (((p1 ∨ (p5 → True)) ∨ False) → p5)) ∨ (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216755508861190009428200419068 : ((((p1 → p4) → p5) ∧ True) → ((((p2 → (p2 ∧ p3)) ∨ p3) ∧ ((p3 → p1) → ((p4 → p4) ∨ p1))) → ((p1 ∧ (p5 ∨ False)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148006184017349606045620718970 : ((((((p1 ∨ (((True ∨ p4) ∧ p4) ∧ p2)) ∧ p4) ∧ (True ∧ (p5 ∧ False))) ∨ (p2 ∧ p4)) ∨ (p2 ∧ False)) ∨ ((False ∨ (True ∨ p1)) ∨ p4)) := by
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
theorem thm_5_vars_204368781754298903535213931252 : (((p3 ∨ ((True ∨ p5) → p4)) ∧ p3) ∨ (((((False ∨ p4) → p4) ∨ p5) → True) ∧ ((p1 ∨ ((((p1 ∨ p3) ∨ p1) ∧ False) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178558173767986020003753308592 : (((((p2 ∨ p3) ∨ (p2 ∨ p1)) → False) ∧ (p3 ∧ ((p5 ∨ p5) ∨ False))) ∨ ((p3 → ((p1 ∨ True) ∨ p5)) ∨ ((p2 ∧ True) → (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172683525566213900086197115613 : (((False ∧ p3) ∨ (False ∨ ((False ∧ (((p5 ∧ False) ∨ (p2 ∧ True)) → True)) ∨ p2))) ∨ ((True → p5) ∨ ((((p5 → p4) ∧ p5) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171576307756356434676219072205 : ((((False ∧ ((False ∨ (True → ((p3 ∨ p5) ∧ False))) ∨ p3)) ∨ (p2 ∨ p4)) ∨ p3) ∨ ((p4 ∨ ((p3 → (False → (True → p3))) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677359101121254307517529164425 : (((((p4 → (p3 ∨ (p2 ∧ ((True → (True → True)) ∧ ((p4 ∨ (p3 ∨ (p4 ∧ p3))) ∧ True))))) ∧ p2) ∨ (False → (p1 ∨ (p3 ∧ p5)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78400616821920439801626251012 : ((((p2 ∨ (((p1 → p1) ∧ ((p1 ∧ (p2 ∧ p2)) → (((True → p5) → (p2 ∨ p5)) ∧ p1))) → (p3 ∧ False))) ∧ p3) ∧ (p2 → p1)) → p2) := by
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
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 → p1) ∧ ((p1 ∧ (p2 ∧ p2)) → (((True → p5) → (p2 ∨ p5)) ∧ p1))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h10.left
      let h17 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h20 := h7 h8
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692228978559178935603997504082 : ((((((p2 ∧ p5) ∨ ((((p2 ∨ (p5 ∧ False)) ∨ p1) ∨ p5) ∨ False)) ∨ False) ∧ (((p5 ∧ ((p3 ∨ p3) → (True ∨ p4))) ∧ False) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206305565366048047364430650357 : ((p1 ∨ ((p4 ∨ (p1 → p5)) → False)) ∨ (((False ∨ (p4 ∨ (False ∨ ((True ∨ (p4 → ((p2 ∧ p1) ∧ (p2 ∧ False)))) → p3)))) ∧ False) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23787507194310527381857340785 : ((((p1 → p1) → (p4 ∨ p2)) ∨ ((p5 → ((((p5 ∧ (p1 ∧ (p1 ∧ p2))) ∨ True) → True) ∨ True)) ∨ ((p3 ∧ p4) → (p4 → p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719470381027185013941694658434 : ((((p1 ∨ (p1 → (p2 ∨ p2))) ∨ ((((p1 ∧ ((p4 ∧ p3) ∨ p4)) ∧ True) ∨ p3) ∨ ((p5 → (p1 ∨ p1)) ∨ (False ∨ (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654261237612997526855120478561 : (((((((((True → p5) → (p4 → (p3 → (True ∧ True)))) ∨ p2) → (p5 ∨ (p2 → (False → False)))) ∧ (p2 → p5)) ∨ p3) ∨ (True ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_314257933459879270983589135095 : (p3 ∨ ((((p1 → True) ∧ (p4 ∧ p2)) ∧ ((p1 ∧ ((p5 ∧ (p4 → (p1 ∧ p3))) → (p2 → p1))) → (p5 ∧ p1))) ∨ (True ∨ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336237131631051269845148066039 : (p1 → ((((p4 ∧ (p1 ∨ (((p4 → False) ∧ ((p5 ∨ False) ∨ p1)) → True))) ∨ ((p2 ∧ p2) ∨ p3)) ∧ ((False → (p3 → p5)) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38167650277944929089934835585 : ((((((p2 ∧ p5) → ((p5 ∨ p1) ∨ ((p3 → p5) ∧ True))) ∧ ((p4 ∨ True) → (p4 ∧ (p4 ∨ p2)))) ∨ ((p5 ∧ p2) → p4)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129090012410492415670919759564 : ((((p2 ∧ (((p1 ∨ (p2 → (True → (p1 → ((p4 ∨ p4) → (False → p4)))))) → p1) → (p4 ∧ p4))) ∨ True) ∨ p3) ∧ ((p2 → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_262195473924115982516346157077 : (True ∧ (((((p2 ∧ p2) ∧ (((p3 → (False ∨ False)) ∨ p1) ∨ True)) → (((False ∨ False) ∧ p5) ∨ ((p4 ∧ False) → (p1 → False)))) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52475877107663629282989037691 : (((p5 ∨ (((p5 ∧ p2) → (((p4 ∧ (p1 ∨ False)) → p2) → p1)) ∨ p4)) ∧ (False → ((p4 ∧ p5) ∧ ((True ∨ False) ∨ (p1 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193518666529137787920481580355 : (((p2 → True) ∨ ((p5 ∧ p5) ∧ ((p3 → True) → p3))) → (p2 ∨ ((p1 ∧ (p3 → p4)) ∨ ((p3 → False) → (p2 → (p2 ∨ (True → p5))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62906806041541025003826691977 : ((p4 ∧ ((p2 ∨ True) → ((((p1 → False) ∨ p1) ∧ (((p3 → p1) ∧ True) ∨ ((p1 ∨ (p2 ∧ p4)) ∧ False))) ∨ (p4 → (p4 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682271046832512876484562846449 : ((((((((p4 ∧ p1) ∧ ((True → p4) → p1)) ∨ (p1 ∧ False)) ∨ (p2 ∨ p4)) ∧ (p3 → p4)) ∧ (p1 ∧ (p2 ∧ ((p3 ∨ p5) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64069279695125654769127466131 : ((False ∨ (((((p3 ∨ False) ∧ ((False ∧ p1) ∧ p1)) ∨ True) ∨ (True ∧ (False → (False → True)))) ∨ ((p4 ∧ (p1 ∧ (p5 ∨ p4))) ∧ p4))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348094813299520351198491562740 : (p3 → ((p2 → False) ∨ ((True → ((p5 ∧ (p5 ∧ ((False ∧ p3) ∧ p3))) ∨ (p5 ∧ p5))) ∨ ((p4 ∨ p4) → ((p4 ∧ p2) ∨ (p3 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113323115266725792652343286171 : ((((True ∧ p1) ∧ (p5 ∨ (False ∨ (((((p3 → ((True ∨ False) ∨ p4)) ∧ p4) ∨ True) ∧ p4) ∨ (False → p4))))) ∧ (p3 ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135143808055264659757814603306 : (((p3 ∨ (p1 ∧ ((((p5 → False) ∨ (p3 ∨ False)) ∧ ((p2 ∨ (True → (p2 ∨ p1))) → p1)) → False))) ∨ (p1 ∨ False)) ∨ (p4 → (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696459897674385269060786918068 : (((((((False → p3) → ((p2 ∧ p4) → p5)) → (p2 ∨ p5)) ∧ p3) ∧ (p5 ∧ (((((p2 ∧ False) → p2) ∨ p4) → True) ∧ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206299300431386656875649552725 : ((p1 ∨ ((p4 ∨ (p3 ∨ p4)) ∨ p5)) ∨ (False → (p4 → (p2 ∧ (((p4 ∨ p2) ∧ ((((p4 ∨ p3) → False) ∨ (False ∨ True)) ∧ p5)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691630441530911033187420715940 : ((((p3 ∧ (True → ((False ∧ True) ∧ ((p3 ∧ True) → ((p4 ∧ (p2 → p5)) → True))))) → (p2 ∧ (((p2 → p2) → (p4 ∨ p4)) ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42414422439980189002130847687 : (((p5 ∧ (((((p3 ∧ ((True → False) ∧ ((((((False ∨ p5) → True) → p3) → p3) ∧ p3) → p2))) ∨ p3) → True) ∧ p5) → p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178868297152689334338010806392 : (((p5 → (p4 ∧ p3)) → (((p5 ∨ p1) ∧ p1) ∨ (p5 ∨ (True → False)))) ∨ (True ∨ (((p4 ∨ (False ∧ p2)) → False) → ((p1 ∧ p3) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69209580482871845025126906988 : ((p5 → ((p3 ∨ (((p5 ∨ p1) → False) ∨ (False ∨ p2))) ∨ (((True → (True ∧ (p1 ∨ True))) ∨ p5) ∧ ((p4 ∨ p4) ∨ (True ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43501295977704652365945414762 : ((((False ∨ (((p1 → (p5 → p5)) ∨ (p3 ∨ (p1 ∧ ((((((p1 ∨ p4) ∨ p2) ∧ True) ∨ p5) ∧ p4) → p2)))) ∨ False)) ∨ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158593034671228889466687416104 : ((False ∧ (((False ∨ ((p2 ∨ False) → p4)) ∧ ((p5 ∧ (((True ∧ p1) ∨ p2) → p1)) ∧ p3)) ∧ p4)) ∨ (((False ∧ p3) ∧ True) → (p1 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775664404227773880529270316420 : (((False ∨ (p1 ∨ (p5 ∧ ((((p1 ∧ ((p5 → (False → False)) → p5)) ∧ (((p5 ∨ False) ∨ (True → (True → p3))) ∧ p3)) → p2) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355577914849518799886587711467 : (p5 → (((((p3 ∧ (((p3 ∨ p5) ∧ (p1 → False)) ∨ p3)) ∧ p2) ∧ (p3 ∨ p4)) ∧ (((p4 → p4) ∧ (p3 ∧ p3)) → True)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215748543615706472484827560133 : ((p1 ∨ ((p4 ∧ False) ∧ p1)) ∨ ((p3 ∨ ((p2 ∧ False) → p1)) ∨ (((p1 → False) → (p3 ∨ ((p5 → p5) → ((p1 → p1) → False)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111008544936229849668102595672 : (((((True ∨ (True ∧ (((p3 ∧ p4) → (True ∨ ((False ∧ p3) ∧ p4))) → (False ∨ p4)))) → p4) ∨ (False ∧ (False ∧ p2))) ∧ p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300680885679935276740588658883 : (False ∨ ((((p5 ∨ p1) ∨ (p1 ∨ (p4 ∨ p5))) ∨ ((p5 → (False ∨ ((p1 → False) ∨ p5))) ∧ False)) ∨ (((p5 ∨ p2) → True) → (True ∨ False)))) := by
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
theorem thm_5_vars_746689511749374972781059858094 : ((((p3 ∨ p2) → ((True → (((False → False) → ((((True ∨ p3) → (p4 ∧ p1)) → False) → False)) → ((p2 ∨ (p2 → p4)) ∨ p2))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145634415094915944710939892391 : (((p2 → (p1 ∧ p4)) → ((p4 ∨ (p5 ∧ ((p1 ∨ (((p2 → (p2 → p1)) ∨ p5) ∨ p3)) ∨ True))) ∨ True)) ∧ ((p1 ∨ True) ∨ (p5 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_172067506652351929058910065601 : ((((p3 → ((p1 ∨ (((False → p2) ∨ p2) ∧ p5)) → p1)) → p1) → (p1 ∧ p4)) ∨ (((p3 ∨ p3) ∧ p3) → ((p5 ∧ p4) → (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606580901792242586942849441885 : (((((((True ∨ ((p3 ∧ p4) → p2)) → (((((p2 → p3) ∧ p5) → (p3 ∧ ((p3 ∧ p1) ∨ p1))) ∧ p4) ∧ p4)) → p1) ∧ p2) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346640862640902253770981458768 : (p3 → ((p4 ∨ ((True ∨ (p1 ∧ p4)) → ((p1 ∧ (False ∧ p4)) ∨ (p2 → (((p4 ∧ p4) ∧ p2) ∧ (p4 ∧ p1)))))) ∨ (p2 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_111716103463851581619841591709 : (((((((True ∧ (p3 → (False ∧ True))) → True) ∨ p1) ∨ (True ∨ (((p1 ∨ (True ∧ True)) ∧ p2) ∨ (p2 ∨ p3)))) → False) ∨ True) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



