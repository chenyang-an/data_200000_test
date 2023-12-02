variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218087330965473112856846484001 : (((True → p2) ∧ (p2 ∧ p3)) → (((False ∧ p2) ∨ (False ∨ ((p4 → (p2 ∨ p5)) ∨ ((p2 ∧ p1) ∧ p3)))) ∧ (((p3 ∨ p4) → p1) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52091184991294169125128739750 : ((((((((p5 ∧ True) → (p2 ∨ (p2 ∧ p1))) → p3) ∨ p5) ∧ (p4 ∨ p4)) ∨ True) → (((False ∨ ((True ∨ p1) ∨ p2)) ∧ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4450785738412173555432510266 : (p2 → (((p5 ∧ (p1 → p4)) ∨ (((True ∧ True) → (p2 ∧ False)) ∧ (((p4 ∨ p2) → ((False → (False ∧ p4)) → p5)) ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81979101940688331623845197540 : ((((p2 ∨ (p2 ∧ ((True → False) ∧ (p2 ∧ p5)))) ∨ ((((True ∧ p2) ∨ p1) ∧ ((p3 ∨ p1) ∨ p4)) ∨ True)) → (p3 ∧ (p5 ∨ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p2 ∧ ((True → False) ∧ (p2 ∧ p5)))) ∨ ((((True ∧ p2) ∨ p1) ∧ ((p3 ∨ p1) ∨ p4)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784564273686608221632652594551 : (((p3 ∨ (p1 ∨ (((((p5 → True) ∧ ((p3 → ((True → p1) ∧ p5)) ∨ (False ∧ (p1 ∧ p4)))) ∨ (p4 → (p2 ∧ p3))) ∨ p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50401509363346933999075914122 : ((((p4 → True) → (p2 ∨ (((p3 ∨ True) → p1) ∧ ((False ∨ True) ∨ ((True → p5) ∧ (True ∨ p1)))))) ∨ (p5 ∧ (True → (p4 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613767338103664445258840579318 : (((((p5 ∧ ((p2 ∧ True) → (False ∨ (p2 ∨ (((p3 ∨ (True ∧ (False ∨ (True ∨ p5)))) → p2) ∨ False))))) ∧ ((p1 → p5) ∧ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159088006979415360930551040195 : ((True → ((((p2 → p3) ∧ ((False → p1) ∧ (p4 ∧ (False ∨ (False ∨ p2))))) ∨ True) ∧ (True → p1))) ∨ ((p2 ∨ ((False ∧ False) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175053687788909760102511805805 : ((p2 ∧ ((p3 ∨ (p5 ∨ False)) ∧ ((((p3 ∨ p5) ∧ p2) ∨ (True ∨ p1)) → p4))) → (((p4 ∨ (p2 ∧ p4)) → (p1 ∨ p3)) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248355070075490899677197248941 : ((p2 ∨ p3) ∨ (True ∧ (((p3 ∧ (p1 → ((p2 ∧ (False ∨ True)) ∧ (False ∨ p2)))) ∨ ((True ∨ (p1 ∧ p3)) ∧ ((p2 → p2) → True))) ∨ p5))) := by
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
theorem thm_5_vars_257029731173579661360117191217 : ((p2 ∨ True) → ((((p2 ∨ True) → False) → (False ∨ p4)) → (((False → (p3 ∧ p1)) → p2) → (((p1 ∧ p1) → p4) ∨ (p2 ∧ (True → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False → (p3 ∧ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111969079106637125862129725823 : (((((p5 ∧ (p2 → True)) → (True ∨ False)) ∧ ((True ∧ (p4 → False)) ∨ (p3 ∧ (p4 ∨ ((True ∧ (True → p5)) ∧ p2))))) ∨ True) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117114707724791804030554343309 : (((p3 → p1) → (False ∨ ((True → (p2 ∨ ((p4 ∧ (p2 → ((False ∨ (p2 → p3)) ∨ p4))) → False))) → ((p5 ∧ p1) ∨ True)))) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264167852816187375449847755207 : (True ∧ (((p1 ∨ p1) ∧ (True ∧ (p1 ∨ (p5 → False)))) ∨ ((p5 ∨ ((p5 ∧ p4) ∨ (False ∨ False))) ∨ ((p4 → (p3 ∨ p2)) → (True ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730840180088701679609350686781 : ((((p5 ∧ (False ∨ p5)) → ((p2 ∨ ((p3 ∨ ((p4 ∨ p1) ∨ False)) ∨ ((((p3 ∧ ((p4 ∨ False) ∧ p1)) → p2) ∧ p1) ∨ False))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343004257265792019585902207427 : (p2 → ((p4 ∨ (False ∧ (p4 ∧ p3))) ∨ (((False ∨ (True ∧ (True → p2))) ∨ ((p5 ∨ True) ∧ (p4 ∨ p2))) ∧ ((p3 ∧ p1) → (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624249552416523127590032581443 : ((((p3 ∨ (((p4 → (p2 ∨ ((p1 → p2) ∨ ((((p2 ∧ p3) ∨ ((False ∧ p2) → p5)) → p3) → p1)))) ∧ (False ∨ p3)) → p5)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41794203025338346774193459646 : (((((False ∧ p4) → (p2 ∧ p1)) → (p1 ∨ (p3 ∨ (((p2 → True) → (p1 → ((p4 → ((p5 → True) ∧ p5)) ∨ p3))) ∧ p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186127085104299020396134165699 : ((((((p5 ∨ p1) → p4) → True) → (False ∨ (p5 ∨ p3))) ∨ True) → (p1 → (((p1 ∧ ((p2 → p2) ∧ ((p1 → p3) ∨ p1))) ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51170036043973727042672476876 : (((((True → (True → ((((True ∧ p4) ∨ p1) ∨ p2) ∨ False))) ∧ (p5 → p1)) ∨ (p1 ∧ p1)) ∨ (((p4 → p4) ∧ (p2 ∧ True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149646609890951830274736649636 : ((p4 ∧ ((p4 ∧ (p1 → ((p1 ∨ (p2 ∨ p2)) → (p4 ∧ p4)))) ∧ (p4 ∧ ((False ∨ (p1 → p3)) ∧ p1)))) ∨ (((False ∧ p5) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166300839573496920689207903013 : ((p4 ∧ (p3 ∧ (((p2 ∨ p4) ∧ ((False ∧ p2) ∨ ((p4 ∧ p4) ∨ p4))) ∨ (p4 ∨ True)))) ∨ (True ∨ (((p5 ∧ p1) ∨ False) ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148464863389686422170313955866 : ((((p5 → p1) ∧ (((p4 ∧ ((False ∧ p3) ∨ p2)) ∨ p4) ∨ p5)) ∧ (p4 → (((p2 → False) ∧ p5) ∨ p4))) ∨ (p1 → (False → (False ∧ p2)))) := by
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
theorem thm_5_vars_266014392719049649402177294735 : (True ∧ (p1 → ((p5 → (((True → p4) → (p4 ∧ (False ∨ (p2 ∨ (p2 ∨ (True ∧ p1)))))) ∧ ((False ∨ False) ∧ True))) ∨ (True → (p4 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775757863962855338440507210747 : (((False ∨ (p4 ∨ ((p4 ∨ ((True → (p5 ∨ ((p3 → ((True → p5) → (True ∨ True))) ∨ p1))) → ((p4 ∧ p2) ∧ (p5 ∨ p5)))) ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_252785873597481902649372938405 : ((True ∧ True) → ((p2 ∨ p3) ∨ (((p5 ∧ ((((False → ((p4 → p3) ∧ p1)) ∨ p3) ∧ p3) ∧ p4)) ∨ True) ∨ (p4 ∧ (p1 ∧ (p3 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42623199242505728422244350864 : (((p3 ∨ (((p2 ∨ (p3 ∧ p3)) ∨ (p3 ∨ ((p3 ∧ p4) ∧ True))) ∧ (p3 ∨ ((((False → False) → (p5 ∨ p3)) ∧ False) ∧ p3)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304783612488229183409078494362 : (p1 ∨ ((p1 → (((p4 → False) ∨ p5) ∧ (False ∧ ((p3 ∨ ((True ∧ ((True → (False ∧ True)) ∨ p1)) ∧ (p4 → p4))) ∨ False)))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356348301824500318150566274828 : (p5 → (((True ∧ (((p1 ∧ True) → (p3 ∧ (p4 ∧ p5))) ∧ (p4 → False))) → p4) ∨ (False ∨ ((p5 ∨ (p3 ∨ False)) ∨ (p1 ∨ (True → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244084742302722838511413678701 : ((True ∧ p3) ∨ ((True ∧ (True → ((((p3 ∧ True) ∧ p2) ∨ (p3 ∨ (p4 → ((p2 ∨ p2) ∨ p4)))) ∨ False))) ∧ (((False ∨ p3) ∧ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113816257253911685260095870998 : (((p2 ∧ (p1 ∧ ((True ∧ p4) ∨ ((p4 ∨ p4) ∧ ((True ∨ (p5 ∧ True)) ∧ (p2 ∧ (False → (True ∧ p3)))))))) → (p3 → p3)) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h15.left
        let h23 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h12.left
      let h26 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Conjunctions on the left can always be decomposed.
        let h33 := h26.left
        let h34 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249506973714056737234565431583 : ((p5 ∨ p1) ∨ ((p2 → p1) ∨ ((p2 → ((p5 ∧ (p3 ∧ (False → (p3 ∧ True)))) → (p1 ∨ ((p4 → p5) ∧ p1)))) ∨ ((p5 ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_65906219666115090915699679430 : ((p4 ∨ (p2 ∧ ((p5 → (((((p2 ∨ False) ∨ (p1 → (p3 ∧ False))) ∧ p2) ∧ (p1 → p2)) → ((True → True) → (p5 → p4)))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219939157535950862953405146645 : ((p4 → (p2 → (p5 ∧ p5))) → (((p1 → (((True → p5) ∨ ((p1 → (True ∨ (p3 ∨ p3))) ∨ p1)) → p2)) ∨ p4) ∨ ((True ∨ p4) ∨ p1))) := by
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
theorem thm_5_vars_702632311441591963987703205008 : (((((p3 → (p2 ∨ (((p3 ∨ p1) ∨ False) → p1))) → False) ∨ ((False → p5) ∨ (((True ∨ ((True ∧ False) → (p1 ∧ p1))) → p5) ∧ p4))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341698464313480626459422713128 : (p2 → (((p1 ∧ (((p2 → (((True → p4) ∨ p3) ∧ p3)) ∧ p2) → (p2 ∨ ((p3 ∧ (p1 ∨ p5)) ∨ p1)))) → (p4 ∧ p5)) ∨ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137369312516754718026770173044 : ((p3 ∧ ((p2 → ((((p2 ∧ True) → (p4 → ((True → True) ∨ p3))) ∧ ((False ∨ True) ∧ False)) ∧ p1)) → (p1 ∨ p5))) ∨ ((p4 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614001737692948365499854453961 : ((((((((p3 → p4) → p3) ∨ False) → (p4 → (p4 → (((False ∧ False) ∧ p5) ∧ ((p3 → p1) → p1))))) ∨ (p5 ∧ (p5 ∧ p5))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352458831980574480843273748819 : (p4 → (((p5 → p4) ∨ p5) → (p3 ∨ (((((p2 → (p3 → (p3 → (((p4 → False) ∧ p4) → p1)))) → p3) ∨ p4) ∧ p4) ∧ (p5 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178233444438246668442403350611 : (((p4 → (((p4 → p2) → (p4 ∨ ((False → p3) ∨ p2))) ∨ p1)) → p1) ∨ ((p5 → ((p4 ∨ p3) ∨ ((p2 ∨ p2) ∧ (p1 ∧ p1)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48173579614786785076422124945 : ((((p1 → p4) ∧ ((True ∧ p5) → ((((((p4 ∨ False) ∨ (((p2 ∧ p5) ∧ p5) ∨ p5)) ∨ p5) → p4) → p1) ∧ p4))) → (p4 → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178628920673640820013238525319 : (((((p5 ∧ True) ∨ p3) ∨ (p5 ∧ p3)) → (((False ∨ p1) ∧ p1) ∨ True)) ∨ (((False ∧ p4) ∧ p1) ∨ (False ∧ (p3 → ((p4 → p1) ∧ p2))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62489736444688314927755019409 : ((p3 ∧ (True ∧ ((((p1 ∨ ((p4 ∧ (True ∧ (p1 → True))) ∨ p3)) ∨ (True ∧ p5)) ∨ (p1 ∨ p3)) ∧ ((p2 → True) → (p2 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715195299167848221051136027556 : ((((False → (((p2 → True) → p1) ∨ p2)) → ((((False → p5) ∧ ((False ∧ True) → p2)) → p3) → ((((p3 ∧ False) ∧ p2) ∨ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159104389069595757818324033717 : ((True → (False ∧ (((p2 ∧ p2) ∨ False) ∨ (((((p3 ∧ p1) ∧ p1) ∨ p3) ∨ (p1 → p4)) ∨ p5)))) ∨ ((((p4 ∧ False) → p4) ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232007286566351869038717745269 : (((p2 ∨ p4) → p1) → ((p4 → (False ∧ p5)) ∨ (((False ∨ ((p3 ∨ False) ∧ p5)) → (p4 ∧ False)) → (p4 → (True → ((p4 ∧ True) ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221751116716062950470435494919 : (((p1 ∧ False) → p2) ∧ (((p4 ∨ (True ∧ (p3 ∨ (p4 → ((False ∨ p4) ∧ ((p3 ∧ p1) ∧ (p1 ∧ (True ∨ p2)))))))) ∧ (p4 ∨ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196130786315558041082268056568 : ((True ∨ ((((False ∨ p1) → p1) ∧ p1) → False)) ∧ (((((p1 ∨ p3) ∧ (p2 ∧ (p5 ∧ (p4 ∧ (p5 → p5))))) → p1) → False) ∨ (True ∨ False))) := by
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
theorem thm_5_vars_54470889580412264613240376230 : (((((p2 → p3) ∧ (p2 ∨ p5)) ∧ (p3 ∧ p3)) ∨ (False ∨ (p2 ∧ (True ∧ (p5 ∨ (p2 → (p5 ∨ (((p5 ∧ p2) ∨ p2) ∨ p4)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161821817206995211951134683759 : ((p5 ∨ (p1 → ((False → ((p3 ∨ p2) ∨ (p5 ∨ (True → (True ∧ (p2 ∨ p4)))))) → (p4 ∧ p3)))) → ((p3 ∧ ((False ∨ True) → False)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305052629631957821388107362323 : (p1 ∨ (((p4 ∨ ((p2 ∧ (((p2 ∧ p5) ∨ True) → False)) ∨ (((p4 ∨ p1) ∧ p3) → (p4 → (p1 → False))))) ∨ p2) → (False ∨ (p3 ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325943719921579556918863563912 : (p5 ∨ (p5 ∨ (((True → (p1 ∨ False)) ∧ p2) ∨ (((False ∧ (((p1 → (p1 ∧ p1)) ∨ (False ∨ p4)) → False)) → (p3 ∨ (False ∧ p3))) ∨ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512151177828316087663918970059 : ((((p2 ∧ p1) ∨ (((False ∧ p1) ∨ p2) ∨ (((((False ∨ p2) ∨ p5) → (p4 ∨ p3)) → p3) → (((p3 ∨ (p2 ∨ p2)) → p4) ∨ True)))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40273561667004577281366955191 : ((((True → ((p2 ∧ (True ∧ (p1 ∨ p4))) ∧ ((False ∨ (((p1 ∨ (p4 → False)) ∨ ((p4 ∧ True) → True)) ∧ p3)) ∧ p1))) ∧ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52004754595261577942799978215 : (((p1 ∧ (p3 → (p1 ∨ (True ∧ (True → ((p2 ∨ (True → (p3 ∨ p1))) ∧ p2)))))) ∨ ((((False ∧ p3) → (False ∧ p1)) ∨ p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135482837822739404383189725485 : ((((((p4 ∨ p5) ∧ p2) → True) → ((p4 ∨ ((True ∨ (False ∧ p4)) ∨ p4)) ∨ (p3 → p2))) → (p2 ∨ (p1 ∧ p5))) ∨ (False → (p2 ∧ p3))) := by
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
theorem thm_5_vars_245706336857037545407653479095 : ((p3 ∧ p2) ∨ (((p4 ∨ (p1 ∨ ((p4 → False) → (((p2 → p1) ∨ ((p2 → False) → (True ∧ (p1 → False)))) ∧ (p4 → False))))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193813601084887807140319417501 : ((p5 ∧ ((p4 ∨ (((p1 ∧ p5) ∨ p1) → True)) → False)) → ((p2 ∨ (((p5 ∧ p4) ∧ p3) → ((((p4 ∧ p1) → p2) ∨ p3) → False))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (((p1 ∧ p5) ∨ p1) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161420746043091496568144085905 : ((p2 ∧ ((((p1 ∧ (p3 ∨ ((((p1 ∧ p5) ∧ p5) ∨ True) → p5))) ∨ (True ∨ p4)) ∨ p2) → p5)) → (((p2 ∧ p5) → False) → (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 ∧ (p3 ∨ ((((p1 ∧ p5) ∧ p5) ∨ True) → p5))) ∨ (True ∨ p4)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39957189230705294540814919832 : (((p4 → (((p2 ∧ ((p5 → p4) ∧ (False ∨ ((True ∧ True) → (p2 → ((p4 → True) → False)))))) ∨ True) ∧ ((p4 → p5) → p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158054892432072287637483986277 : (((p1 ∧ (p4 ∧ ((p4 ∧ False) ∨ p3))) ∨ ((p3 ∧ False) ∨ (((p5 → (p1 → p3)) ∨ p1) ∨ False))) ∨ (True ∨ (((p4 → p1) ∧ p1) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230657731050753787997560591526 : (((p3 → p2) ∧ p1) → (((p4 ∧ p4) → False) ∨ (((False ∧ (p1 ∧ p2)) ∨ p2) ∨ (False ∨ (p1 ∨ ((p3 ∧ (p5 → p5)) → (p3 ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68035449515201773147088310654 : ((p2 → (p2 ∧ (p1 ∨ ((p3 ∨ (((p4 → (True ∧ (False → (p4 ∧ False)))) ∨ ((p2 ∧ (p5 → True)) → p2)) → (p5 ∨ p5))) ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50748163327636377647254272881 : (((p3 ∧ ((((p4 ∨ (p5 ∧ (p1 → True))) ∧ ((p5 ∧ (p5 → p5)) ∧ p4)) ∨ (False ∨ p1)) → p2)) → (p5 ∧ ((p5 ∧ p1) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306636426439904118966941155358 : (p1 ∨ (True ∧ (((p2 → p4) → (((p3 ∧ p3) ∨ ((p4 ∨ p3) ∨ (((False ∧ p2) ∧ (p4 → (p4 → p5))) ∨ (p3 ∨ False)))) ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_49780562178246359366849922962 : (((p3 ∨ (((((False → p2) ∨ (((p5 → p1) ∧ False) ∨ (((True ∨ p4) ∨ p3) ∨ False))) ∧ p2) ∧ True) → p1)) → (p2 ∨ (p3 → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158557949872001724367815944445 : ((True ∧ ((((p5 → p1) → (((True → (p3 ∧ p5)) ∧ (p2 ∧ False)) ∧ (p4 ∨ p3))) ∨ False) ∨ True)) ∨ (((False ∨ (p4 → p3)) ∨ p2) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90813845609838588129329973652 : (((p3 ∨ p2) ∧ (((p2 ∨ (False ∨ ((p5 ∨ p2) → ((p1 ∨ (False ∨ False)) → p3)))) → False) ∧ (p4 ∧ ((p3 ∨ p1) → (False ∨ p2))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h14 : (p2 ∨ (False ∨ ((p5 ∨ p2) → ((p1 ∨ (False ∨ False)) → p3)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h15 := h10 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134821652209656518606171884883 : (((False ∨ ((p5 ∧ True) ∧ (p2 → (p5 ∨ (True ∧ ((((True ∨ True) ∨ p4) ∧ (True ∨ True)) → (p3 ∨ p4))))))) → p4) ∨ (True ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123976007024133849097104638706 : ((((((False ∧ ((p1 ∧ p5) → False)) → False) ∨ (p4 ∧ p2)) → p1) ∨ ((p4 ∨ ((False → True) ∨ (True ∨ p4))) → (False ∧ p3))) → (p4 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((False ∧ ((p1 ∧ p5) → False)) → False) ∨ (p4 ∧ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p4 ∨ ((False → True) ∨ (True ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324635151993045880545125526796 : (p5 ∨ (((p4 ∧ True) ∧ p5) ∨ (p2 ∨ (((((p4 → (p1 ∨ True)) ∧ ((p2 ∨ True) ∨ p3)) → (True → p2)) → False) → (p2 → (p1 ∧ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 → (p1 ∨ True)) ∧ ((p2 ∨ True) ∨ p3)) → (True → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h3
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (((p4 → (p1 ∨ True)) ∧ ((p2 ∨ True) ∨ p3)) → (True → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h13
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753300725310041217259796700456 : (((False ∧ (((p1 ∨ ((p1 → (p2 ∧ (p5 ∨ (p3 → False)))) → ((p1 ∨ (p2 ∧ ((True ∨ p5) → p5))) ∨ p1))) → True) → (p4 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319464403767575857412861333836 : (p4 ∨ (((True ∧ p1) → ((p5 ∧ ((p1 → (p4 → True)) ∨ p3)) ∧ p5)) ∨ (p2 ∨ (((p3 → p3) → (p2 ∧ (p1 ∨ (p2 → False)))) ∨ True)))) := by
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
theorem thm_5_vars_161007981245969228581059737205 : (((False ∧ (True ∧ p3)) ∨ (((p3 ∨ False) ∧ p4) ∨ ((((False ∨ p4) ∧ p3) ∧ p3) → (p2 → p5)))) → ((True → p2) → ((p3 ∨ p5) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h14 := h2 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h28 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h29 := h2 h28
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h33 := h2 h32
        -- One of the premise coincides with the conclusion.
        exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644700885650779695182745014708 : ((((p1 ∨ (p1 ∨ (((((p5 ∨ p2) ∧ (p2 ∧ p2)) ∨ ((p1 ∨ ((p1 ∨ (False → p2)) → False)) ∨ (p5 → p2))) ∨ p1) ∧ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246144715340278992648484753631 : ((p4 ∧ p2) ∨ ((True → (p1 ∧ (((p4 ∧ p3) ∨ True) → (((p1 ∨ (True ∨ ((p2 ∧ (p4 ∧ p2)) → p3))) ∧ p1) ∨ p3)))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55592480454787970868642970404 : (((p4 ∨ ((p4 ∧ p3) ∨ (p1 ∧ p3))) → ((False ∧ (p5 → ((p5 → (p2 ∨ True)) → ((p4 ∧ (p4 ∨ p3)) ∧ (p1 ∨ p4))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200935259022660408156724930294 : ((p1 ∨ (False ∨ ((p1 → p2) ∧ (p1 ∨ False)))) → ((p2 → ((p2 → p4) ∨ ((p4 ∧ (p2 ∨ p2)) → True))) ∨ (p2 ∧ ((p2 ∧ True) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53290679900040943393169868025 : (((False ∨ ((((False ∧ ((p4 → p3) → False)) ∧ p3) → p2) → p4)) ∨ (p4 → (False → (((p1 ∧ p5) ∨ (p2 → p4)) → (p2 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684953355115608455935119397392 : ((((p2 ∧ (p3 ∨ (((p4 ∧ (p4 → False)) ∧ (((p3 → (p4 → p4)) ∨ True) ∧ p3)) ∨ p4))) ∨ ((p4 ∨ p4) → (True ∧ (p4 ∨ p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160482131287847202749774331652 : (((p2 → ((p2 ∧ (((p5 ∨ (p4 ∨ True)) → p5) → p3)) → (p5 ∧ p2))) → (True ∧ (p1 → p1))) → (p4 → ((False ∨ p3) → (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199279063356335537724303077283 : (((((p3 ∨ p4) → (p1 ∨ p2)) ∧ p4) ∨ False) → (((False ∨ ((p2 → p1) ∨ p2)) ∨ ((p3 ∨ (((False ∧ p3) ∧ p5) ∨ p4)) ∨ False)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146944175881035863894190926750 : (((((p2 → ((((p2 ∨ (False ∧ (p3 → True))) ∨ True) ∨ False) ∨ p1)) ∧ ((p1 ∨ p1) ∨ False)) ∨ p4) ∧ False) ∨ (False → (p1 → (p3 ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54611070479057935152441747561 : (((p4 → (((p1 ∧ (True ∨ False)) ∧ p3) ∧ p4)) ∨ (((False ∧ ((((p3 → p1) ∧ p5) → False) → p1)) ∨ (False ∨ p2)) ∨ (False → False))) ∨ False) := by
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
theorem thm_5_vars_194647077626838523150359058616 : (((((p3 → False) ∧ p4) ∧ (p1 ∧ p1)) ∨ True) ∧ (((p5 → p3) ∧ (p5 ∨ (p4 → True))) → (p3 ∨ (((False → True) ∨ (p5 → p5)) ∨ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317883374985385674294965203047 : (p4 ∨ ((True ∧ ((p2 ∧ ((p3 → p1) ∧ (p1 ∧ p3))) ∧ (p3 ∧ (((((((False ∨ p5) → p2) → True) ∨ p5) ∧ p5) ∧ p4) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162520870129864722554921500980 : (((True → (True → ((True ∨ (p5 ∧ p2)) → ((p1 ∨ p1) ∨ ((p1 ∧ p5) → p4))))) ∨ True) ∧ (p5 ∨ (p3 ∨ ((p3 → p1) ∨ (p3 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_561844285745130756801460735470 : (((p5 ∨ (((p1 ∧ ((p1 ∨ ((p1 ∧ (p4 → (p3 ∧ False))) ∧ p5)) ∨ (p2 → (p3 → ((False ∨ False) ∨ p4))))) ∨ (p1 → True)) ∨ p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113197502395245146754855464012 : (((((((True → (p1 ∨ ((p4 ∧ p3) ∧ (p4 ∨ (((p4 ∨ p5) ∨ p2) ∧ True))))) → p1) ∧ True) ∧ p3) ∨ p2) ∧ (p1 ∧ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206292871427650507259395863218 : ((p1 ∨ ((p3 ∨ (p3 ∧ p3)) ∧ False)) ∨ (((((p5 ∧ p2) → (p1 ∧ (p3 → ((False ∧ False) → p2)))) ∧ p3) ∨ True) → ((False ∧ p3) → p4))) := by
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
theorem thm_5_vars_42353555457008139952122353321 : (((p3 ∧ ((False ∧ True) ∧ ((p5 ∧ ((True ∨ (True ∨ (p5 → (((p5 ∨ p2) → ((p2 → p2) → p5)) ∧ p2)))) ∨ p2)) ∧ p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118715256950300170959816653958 : ((p5 ∨ (((((((True ∧ (p1 ∧ p2)) ∧ p3) ∧ ((p3 → ((False ∨ p5) ∧ p3)) ∨ p3)) ∧ p5) → p1) → p1) ∨ (p5 ∧ p3))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249840563191306814155717607249 : ((True → False) ∨ ((p5 → ((p5 → p1) ∨ ((((p3 → (p1 ∨ (p5 → p4))) → p5) ∨ ((p2 → p2) ∧ (p3 → (p2 ∧ p4)))) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119486176249218380892893673583 : ((p4 → (p1 ∨ ((((p2 ∨ p4) ∨ ((((p4 ∨ True) → (False → True)) ∧ False) → (p2 ∨ (False ∨ p5)))) ∧ (p5 ∨ p5)) ∧ p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117215181475500587998281541439 : ((True ∧ ((False → (False ∧ p2)) ∧ (p1 ∨ (p2 ∨ ((True → (p4 ∧ ((False → (((False → p2) → p5) → p3)) ∧ p3))) → p3))))) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39964180748548517932181054694 : (((p4 → ((((p5 ∨ p5) ∨ p1) ∧ (False ∨ p2)) ∧ (((p5 ∧ True) → p1) ∧ ((((True → (p1 → p2)) → p5) → p2) → p5)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225383681543315810384290123885 : (((p2 ∨ p2) ∧ p2) ∨ (((p4 ∨ p2) → ((((p4 ∨ (((p3 ∧ ((False ∧ p2) ∧ p4)) ∨ p5) ∧ p2)) ∧ p5) ∧ p4) ∨ (p5 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105649823699825912257798620526 : ((((((p4 ∨ (p4 ∧ (p5 ∧ p1))) → False) ∨ False) ∨ (((True → True) ∧ p1) → True)) ∧ ((p4 ∨ ((p3 ∧ p3) ∨ True)) ∨ p2)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206326905274647009116566141742 : ((p1 ∨ (p4 ∨ ((True → p1) ∧ False))) ∨ ((True → (((p5 ∧ ((p5 ∨ (p1 ∧ p4)) → True)) ∧ ((p3 ∨ (p3 ∧ p5)) ∧ p4)) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311804751913898012612264420495 : (p2 ∨ (p1 ∨ (((True ∨ ((p1 → (p2 ∨ p3)) → ((True ∧ p3) ∧ (p2 ∧ p4)))) → (True ∧ (p5 ∨ ((p1 → (p5 ∨ p4)) → False)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



