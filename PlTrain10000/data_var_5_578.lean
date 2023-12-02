variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586244298274966533852289483571 : ((((((((p5 → p3) ∧ ((p4 ∨ p1) ∧ (p4 → p5))) ∨ p3) ∨ (p4 ∨ (p1 → ((p1 ∧ ((p1 → p4) ∨ p2)) ∧ p2)))) ∧ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167272349267127292191338040519 : (((((((p1 ∨ p3) ∧ (p3 ∧ (True ∧ ((p2 ∨ True) ∧ False)))) ∨ p4) ∧ p4) ∨ p5) → p5) → ((((True → p4) ∧ p2) ∨ True) ∨ (True ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110953688281788175333496467351 : (((((((p5 ∨ (p2 ∨ (p1 → (((p4 ∧ ((p4 ∧ p3) ∧ p1)) ∧ p1) ∧ True)))) ∨ p2) → p3) → p5) ∨ (p2 ∨ p5)) ∧ False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38316783998245428825918465501 : (((((p4 ∧ p1) ∧ ((((False → p4) ∨ (p5 → False)) → ((False → p1) → True)) ∨ (True → p4))) → (((p4 ∧ p1) ∧ p5) ∧ p2)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257852419903576870293144988786 : ((p4 ∨ True) → ((((p4 ∧ ((True ∨ True) ∧ ((((((p4 ∨ p3) → p5) ∨ p3) ∨ False) → (True ∨ (p2 ∨ p2))) ∧ True))) ∨ p1) → p2) ∨ True)) := by
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
theorem thm_5_vars_303188678053763715245178862525 : (False ∨ (p4 → (((p3 → True) → ((((p5 ∨ p5) → False) ∨ p1) ∨ p1)) ∨ (p5 ∨ (p1 → ((((p3 ∨ p1) → p2) ∧ False) → (p2 ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330746585003056329695990173046 : (True → (p1 → ((p3 ∧ ((p5 → True) ∨ (p4 ∨ (p1 ∧ True)))) → (((p4 ∧ ((((p2 ∧ p2) → p4) ∧ (p4 ∨ p1)) ∧ p5)) ∧ True) ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193779218172971641236438830662 : ((p4 ∧ (((p2 ∧ (p1 → (p3 ∨ True))) → p2) → False)) → (((p5 → ((p2 → p5) → (p3 → ((True ∨ True) ∧ False)))) → p1) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ (p1 → (p3 ∨ True))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19076114539622435423112329170 : (((((((p4 → (p1 → p5)) ∧ (p3 → (p3 → (False ∨ False)))) ∧ p4) ∨ p2) → (False ∧ False)) → (p2 → (((p3 → p1) → False) ∧ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 → (p1 → p5)) ∧ (p3 → (p3 → (False ∨ False)))) ∧ p4) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47009844108362999963303873858 : ((((True ∧ ((p3 → (p5 → (True ∧ (p5 → (p2 → ((True ∧ (p5 → p1)) → False)))))) ∨ ((p5 → p5) → p2))) → False) ∨ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207291895467944780392484268174 : ((((p5 ∧ (p2 → p2)) → False) ∨ p3) → (((p4 ∨ (True → ((p3 ∧ (p2 ∧ (p5 → p3))) ∨ p4))) ∨ (((False → False) ∨ p2) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_228181354714991065048216539161 : ((p5 ∧ (p2 ∧ p5)) ∨ (p3 ∨ (((((p3 ∧ (p2 ∧ (p4 → p4))) ∧ False) ∨ True) ∧ (True ∨ p5)) ∨ (p1 ∧ ((p3 ∧ (p5 ∧ p3)) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759939199583159133090545816320 : (((p2 ∧ ((p1 ∨ ((p3 ∧ False) → (p1 → p5))) → ((((True ∨ ((p1 ∧ p3) → (p2 ∧ (p5 ∨ p5)))) ∧ (p1 ∨ False)) ∨ p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174371200074019940993114983396 : (((((p4 → (p4 → (p5 ∨ p3))) → p1) ∧ p5) ∧ ((p3 ∧ (True ∧ p3)) → True)) → ((((p2 ∧ p4) → (p2 ∧ p4)) → (p5 ∧ p3)) ∨ p1)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → (p4 → (p5 ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165577208650444373459996773590 : (((((p1 ∨ p1) ∧ p3) → ((p4 ∨ p4) ∨ False)) ∨ ((p3 → (p4 ∧ p3)) ∧ (p1 → True))) ∨ (p2 → ((False ∨ False) → ((False ∨ p2) ∨ p2)))) := by
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
theorem thm_5_vars_207998274490481477612427344898 : ((((False → False) ∨ p1) ∨ (p2 ∨ p1)) → ((p5 ∧ ((p4 → (p4 ∨ (p2 → p4))) ∧ (((p4 ∨ (p1 ∨ p4)) → (False ∨ p2)) → p5))) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174869071835642323646468302937 : (((p1 → True) ∨ (p4 ∧ ((False ∨ p5) → ((p1 → (p2 ∨ (p5 ∧ p3))) → p2)))) → ((True → False) → (((p2 ∧ p2) ∧ (p2 ∧ p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222182340740055934355167163683 : (((p5 ∨ False) → True) ∧ (p1 → ((p2 → (True → ((((False ∧ p2) ∧ (((p3 → p3) → (p1 ∧ p5)) ∧ p5)) ∨ (False ∨ True)) ∨ False))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37475490810106290741928664088 : ((((((False ∨ p5) ∨ (p3 → (False → p2))) → (p1 ∧ (p1 ∨ (((True ∧ p2) → (((p2 ∨ p3) ∧ p3) → p1)) ∨ p1)))) ∨ p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243289559059290397076130552438 : ((p4 → p4) ∧ ((((((p5 ∧ ((True ∨ p5) ∨ False)) → ((False ∧ p1) ∧ p5)) → p4) → (p3 ∧ p2)) ∧ (p4 ∧ (p3 → p1))) ∨ (p5 → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316611515453337059376340064467 : (p3 ∨ (p4 ∨ ((p1 ∧ (p3 ∨ (((True ∧ p1) ∨ ((p5 → ((False → (False → p1)) ∨ p1)) ∨ p3)) ∨ ((p2 → p4) → (False → True))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721667253334617820125381317097 : ((((True ∨ (p3 ∨ (p1 ∨ p3))) → ((p3 ∨ (p5 ∨ ((((p3 ∧ p4) ∧ p1) ∧ p1) ∨ (p1 ∨ True)))) ∨ (True ∨ (p5 ∧ (p4 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113477213824721666533991966009 : ((((p2 ∧ ((((p5 → ((p4 → p2) → p3)) ∨ (False ∧ True)) ∨ (p4 ∧ p3)) → (p4 ∧ p5))) ∧ (p3 ∧ p1)) ∨ (p1 ∧ p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115477970609400135777003306847 : (((p2 → (((p3 → p1) ∧ (p5 ∨ False)) ∧ False)) ∨ ((((False ∨ p3) ∨ p4) ∧ (p5 ∧ (p1 → ((p3 → False) ∧ p2)))) ∧ False)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41545137568579556707633951319 : ((((True ∧ (p1 ∨ (p4 ∧ (p4 ∨ ((True ∨ p2) → p1))))) ∨ (((((True ∨ False) ∨ (p4 ∨ p4)) → (False ∧ p1)) → p5) ∨ p5)) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ False) ∨ (p4 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223387242845483297109141968290 : ((True ∨ (p4 ∨ p1)) ∧ (p3 ∨ ((p5 ∨ (p2 → ((p3 ∨ (p5 ∨ (p5 ∨ (False → (p5 → False))))) ∨ ((p2 → p2) → False)))) ∨ (p5 ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621886814947498983875202015120 : ((((p1 ∧ ((p4 → (p4 ∨ True)) → ((((p1 ∨ p4) ∧ p3) ∧ (p2 ∧ p3)) ∨ ((True → ((p3 ∧ p3) ∧ False)) → (p5 → True))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613311078861154670081570624930 : (((((((p2 → p5) ∨ False) ∨ ((p2 ∨ ((((True → p3) ∧ p4) → False) ∧ (p3 ∨ (p4 → p5)))) ∧ (p1 ∨ p4))) → (p2 ∧ p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719759909375384556211474436187 : ((((p1 → (False ∧ (True ∨ p3))) ∨ (((p4 → p4) ∧ p2) ∨ (((((p3 ∧ (((True ∨ p4) → p3) ∨ True)) ∧ p1) ∧ p4) ∨ True) ∨ p2))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54084751361252350789382520417 : ((((True ∨ p1) ∨ ((True ∧ (p2 ∨ p5)) ∨ (p3 ∨ p2))) → (True ∧ (p3 → (((p1 ∨ (True → p3)) ∨ (p4 ∨ p3)) ∨ (p4 ∨ p5))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152028981856899639779736859126 : ((((p5 → (True ∨ (p3 ∨ (p1 ∧ False)))) → (True ∧ True)) ∧ (False → (p3 ∧ (p2 ∧ ((True ∨ p4) → p3))))) → ((p2 ∨ p2) → (p3 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346756747604696809058543234894 : (p3 → ((True → (((((p5 ∧ p5) ∧ p3) → p1) → ((((p1 → p5) → p4) ∧ (False ∨ p5)) ∨ True)) ∧ True)) ∧ ((True → True) ∨ (p1 → p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168228526422929849840230144518 : ((((p1 ∧ False) ∧ p4) → ((p5 ∨ ((p1 ∨ True) → p3)) ∧ ((p3 → p1) → (p3 ∨ p4)))) → (p5 → ((True ∨ p4) ∧ ((p3 ∧ p2) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225408895675090593122507499686 : (((p3 ∨ True) ∧ p5) ∨ ((((p2 ∨ (p1 → p1)) ∨ p1) → False) ∨ ((False → (False ∨ ((p1 ∧ ((p5 ∧ p2) → p3)) ∨ p4))) ∨ (p4 ∧ p1)))) := by
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
theorem thm_5_vars_111694474030026628964206122002 : ((((((p3 ∨ ((p1 ∨ (False ∨ (((p3 → p2) ∨ False) ∧ p1))) ∧ p1)) ∨ (((True ∧ p4) ∧ p3) → p4)) → False) → p1) ∨ p4) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((p1 ∨ (False ∨ (((p3 → p2) ∨ False) ∧ p1))) ∧ p1)) ∨ (((True ∧ p4) ∧ p3) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135776231190762024242674819227 : (((((((((p4 → p4) ∨ (True → False)) → p3) ∨ p2) → p2) ∨ p5) → p1) → ((((p5 ∧ p2) ∧ p4) → True) → p3)) ∨ (p5 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596375104798044260419077584328 : ((((((True ∧ (True → False)) ∨ ((p3 ∧ p1) ∨ p5)) ∨ (p2 ∨ (p5 ∨ (((p4 → (True ∧ p2)) → (True ∧ (p2 ∧ p1))) ∨ True)))) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649794707463942924287618674383 : ((((((True → (p1 → p2)) ∨ (p2 ∧ (((p3 ∨ (p4 ∨ p5)) → ((p4 → p1) → (p1 → True))) ∧ True))) → (p2 → p2)) ∧ (True ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1802195102795375909656079852 : (((p4 ∨ p2) ∨ (p1 ∨ (p3 ∨ (((True ∧ p4) → p4) → (p4 ∧ ((((p3 → p3) ∧ p4) → p4) → p5)))))) ∨ (True ∨ (False ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52535591885452670562083977403 : ((((p1 ∧ ((p2 → ((((True ∧ p3) ∧ p4) → p1) → False)) ∨ False)) ∨ True) ∨ (((p1 → (p1 ∨ p2)) ∧ False) ∨ (p1 ∨ (p5 ∧ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613920153173415385706177188301 : ((((((False ∧ (p2 ∨ (p4 → ((p5 ∨ ((p2 ∧ (p5 ∨ p5)) → p1)) ∧ (True ∧ p2))))) ∧ (p4 ∨ False)) ∨ ((False ∧ False) → False)) ∨ p5) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698622090949272697428507421142 : (((((p5 → (False ∨ False)) ∧ ((True ∨ ((p3 ∧ p2) ∨ False)) ∧ False)) ∨ (p3 ∨ ((p1 → ((p4 ∧ p1) ∧ False)) ∧ ((True ∧ False) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50522118563032455930553484620 : ((((p1 ∨ (p2 ∨ ((p5 ∧ (p1 ∨ (p3 ∨ p3))) ∧ (True ∨ (((p1 ∧ p2) ∨ p2) ∧ p2))))) ∧ p3) → ((True → p3) ∧ (p4 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54493551359744173739837884529 : ((((p4 → ((True ∨ p5) → True)) → (p1 ∨ p5)) ∨ (((p3 ∨ (False ∧ (p3 → ((p4 → ((True ∨ False) ∧ p4)) ∧ p3)))) ∨ False) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60691574081153184794837448075 : ((True ∧ (((p3 ∨ False) → (p2 ∨ (p5 ∧ (((p1 ∨ p3) ∧ True) ∧ True)))) → ((False ∨ p3) ∨ (p5 ∨ (False ∨ (p4 → (True → p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42930875735334513523499034337 : (((p4 → ((((((p1 → p4) ∧ ((((False ∧ (p3 → p1)) ∧ p3) ∨ True) ∧ (p1 → p3))) ∧ p1) ∨ p5) ∨ p2) ∨ (True → p4))) ∨ p2) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638047921537760242492211143769 : ((((((p1 → p3) ∧ ((p1 → p5) → (p5 ∧ False))) ∨ (((p2 ∨ p2) ∧ ((False → ((p4 ∨ True) ∨ False)) ∧ (p1 → p4))) ∨ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825603882558959856537396701056 : (((((True → False) ∧ ((p5 → ((p4 ∧ p1) ∧ (True → p3))) ∧ ((p3 ∧ (p1 → p5)) → (((p2 ∨ p3) ∧ (p3 ∧ True)) ∧ p2)))) ∧ p1) → p2) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38087334533928878894175831267 : ((((p3 ∧ (p4 → (((True → (False ∧ p2)) ∧ (True ∧ (p2 ∨ p2))) ∨ (((p1 ∨ (False → p4)) ∧ p4) ∧ p4)))) → (p1 ∧ True)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262518425425902497193743410212 : (True ∧ ((p5 → (((p3 ∨ (p4 ∧ ((p2 ∨ False) ∧ (p4 → ((True → p2) ∨ (p4 ∨ (p4 → p3))))))) ∨ p4) → ((p5 ∧ False) ∨ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178673755105742148836517109908 : (((False ∨ ((False ∨ p1) ∨ False)) ∧ ((p3 ∨ (True ∧ True)) ∨ (True → True))) ∨ (True ∨ (False → ((False ∧ p4) ∨ (((True ∨ p4) ∧ False) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187655850105266031050840595401 : ((True → ((True ∨ (((p1 ∧ False) → p1) ∧ (False ∧ True))) ∧ False)) → (p4 ∧ ((((p4 ∨ (p3 ∨ (True ∧ p1))) → p2) → (p3 ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44094056530551177091560513034 : ((((p4 ∨ ((((True ∨ p2) → True) ∧ (p3 ∨ True)) → ((p2 ∨ (p4 ∨ p4)) → ((True ∨ p2) → True)))) ∧ ((p3 ∧ p2) ∨ p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303961582482563083959097955647 : (p1 ∨ ((((False ∧ p2) → p2) ∧ ((p4 ∨ p4) ∧ (((True ∨ (((False → False) ∧ p4) → p5)) ∧ (((False → p1) ∨ p2) → p4)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147424033315421297182077071489 : (((((p3 ∧ False) ∧ p5) ∨ (((p5 ∧ ((((p2 → p4) ∨ p2) ∧ False) → p4)) → p5) → (p4 → p3))) ∨ p4) ∨ (False → ((p3 ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135234863096958491817949846030 : ((((p3 → ((p2 ∧ p2) ∧ True)) ∨ ((p4 → (True ∨ (p5 → p2))) ∧ (((p5 ∧ True) ∨ True) → True))) → (p1 ∧ p4)) ∨ ((False ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936488139487919901763778081198 : ((((((p5 ∧ (False ∨ p1)) → p3) ∧ p3) ∧ (p5 ∨ (p4 ∨ (((((p3 ∧ p3) ∧ True) ∧ p1) ∨ p3) ∧ (p1 ∨ (p4 → (p1 ∧ False))))))) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h23 =>
          -- One of the premise coincides with the conclusion.
          exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117178498329432194566137829841 : ((True ∧ (((p1 → False) ∨ (p1 ∧ (((p5 ∨ ((p3 ∧ True) ∧ p2)) → p4) ∨ (p1 → ((p5 ∨ p1) ∧ p3))))) ∧ (p2 ∨ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207510913830789947843775435148 : (((((p1 ∧ p1) ∨ p2) ∧ True) → p4) → (p2 ∨ (((p3 ∨ (p1 ∨ p2)) ∧ ((p2 → (p4 ∨ (((p4 ∨ p4) ∨ p5) ∨ False))) → False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → (p4 ∨ (((p4 ∨ p4) ∨ p5) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (((p1 ∧ p1) ∨ p2) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h6
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : (p2 → (p4 ∨ (((p4 ∨ p4) ∨ p5) ∨ False))) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : (((p1 ∧ p1) ∨ p2) ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h14
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117162312713288542922459772242 : ((True ∧ ((True ∧ ((False ∧ ((p5 → ((p1 ∨ p2) → (p2 ∨ False))) → p2)) ∨ ((True ∨ ((p3 ∧ False) ∧ p3)) → p1))) ∨ p4)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233184503917992847763257458737 : ((p5 ∧ (p3 ∨ p4)) → (((((((p4 ∧ False) ∧ ((p5 ∨ p1) ∨ True)) ∨ p5) ∨ (p3 → (p1 ∧ p2))) ∨ ((False → p3) ∨ False)) ∧ p1) ∨ True)) := by
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
theorem thm_5_vars_228449525435460895454322619840 : ((False ∨ (p1 ∨ p3)) ∨ ((p3 ∨ p1) → (True → ((p3 ∧ p5) → ((p4 → (p4 → True)) → ((False ∨ (p3 → p5)) ∨ ((p3 ∨ True) ∨ p3))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53314453986546012722293417278 : (((p1 → (((True → (p5 ∨ p3)) ∨ ((p3 ∨ p3) ∨ p5)) ∨ p3)) ∨ (((p2 ∨ (p5 → True)) ∧ (((p3 → p2) ∨ p5) → p5)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181998727757437733919406656996 : (((((((True ∧ p4) ∧ p4) ∧ False) → p4) ∧ (p3 ∧ p5)) ∨ True) ∧ (True → ((((p2 ∧ p3) ∨ (p1 → p3)) ∨ (p2 ∧ p1)) ∨ (True ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84501075941174497314710283426 : (((((p4 ∨ p3) ∧ (((False ∨ ((p2 → p3) ∨ p4)) ∨ p2) ∨ p3)) ∨ (True ∨ p2)) → ((p3 ∧ (True → True)) ∧ (False ∧ (p5 → p2)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p3) ∧ (((False ∨ ((p2 → p3) ∨ p4)) ∨ p2) ∨ p3)) ∨ (True ∨ p2)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782479432945775657364275565296 : (((p3 ∨ (((True ∨ (((p5 ∨ p2) ∧ (p4 ∨ p5)) → p1)) → ((p4 ∧ ((p2 ∨ (((p4 → p2) → p2) ∨ True)) ∨ p3)) ∨ p2)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_175573288219105342713139792874 : ((p5 → (p4 ∨ (p2 ∧ ((True ∨ ((p2 → p5) ∨ (p4 ∨ (p5 ∨ p4)))) ∨ True)))) → ((True → (p5 ∧ (p2 ∧ p3))) → ((p4 → p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117661050051873873905807169403 : ((p3 ∧ (((p2 → p1) ∨ ((p1 ∧ (((((True → True) → p4) → p1) ∧ (True → True)) → p1)) ∨ False)) ∨ (p2 ∧ (p5 ∧ p1)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51307027646995705461039214030 : (((p2 ∨ ((p3 ∧ (((True ∨ (False ∧ False)) → p1) ∨ ((p1 ∨ p5) ∨ (p5 ∧ p4)))) ∨ False)) ∨ (p1 ∧ ((p3 ∧ (p1 → p1)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206354925934024405421276250445 : ((p2 ∨ ((p1 ∨ p3) ∧ (p3 ∧ p2))) ∨ (((((True ∨ (p2 → p1)) → False) ∧ p4) → (True ∨ ((p2 → p1) ∧ (p2 → (p4 ∨ True))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178075377833313283653496609599 : ((((p3 → ((True ∧ p4) ∨ (p4 ∧ ((p1 ∨ True) ∧ True)))) ∨ p2) → p3) ∨ (p1 → (False → (p1 ∨ (True ∧ (True ∧ (p3 → (p2 ∧ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149778389445824408839652630066 : ((False ∨ ((p3 → ((((p2 ∧ False) ∨ p5) → ((p5 ∨ ((p4 ∨ p2) ∨ False)) ∨ p5)) ∨ (False ∨ p2))) → p1)) ∨ (p5 ∨ (False ∨ (False → False)))) := by
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
theorem thm_5_vars_442987254229479665291882290281 : (((((((p4 → p3) ∧ False) ∨ (((False → True) → (p3 → (p1 ∧ ((p4 ∨ False) → True)))) → p2)) → (p5 → p1)) ∨ (p4 → (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_606604385400356618134288270016 : (((((((p5 → p5) → (False → (p2 ∧ (p4 ∧ (p3 ∧ ((p4 ∧ True) → ((p1 ∨ (p1 ∨ (p4 ∧ p5))) ∧ p4))))))) → p3) ∧ p2) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263620859096236723962743200012 : (True ∧ (((p3 ∨ (False → p1)) ∧ ((False → ((p5 ∧ (p4 → (p4 ∧ p4))) ∧ p5)) ∧ ((p4 ∨ p4) ∧ p2))) → ((p1 ∨ p3) ∨ (True ∧ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41377483233633989973904254049 : ((((True → ((p4 ∧ False) → (((False ∧ False) ∨ p1) ∨ ((p5 ∧ p3) ∧ (p3 ∧ True))))) → (((True → p2) ∨ p4) → (p1 ∧ p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149821835650058369634533662080 : ((p1 ∨ ((((((p2 ∧ ((p1 ∨ (False → (p1 → p4))) ∨ True)) → True) ∨ p3) → (p4 ∨ True)) → p1) → p1)) ∨ (((True → False) ∨ p1) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ ((p1 ∨ (False → (p1 → p4))) ∨ True)) → True) ∨ p3) → (p4 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119285477461540854606766868605 : ((p3 → (((p1 → (p3 → (p2 → (True → (p3 ∨ True))))) ∧ ((((False ∧ (p5 → False)) ∨ False) → p3) → (True → False))) ∨ True)) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150033713844076365887420646890 : ((p5 ∨ (p1 ∧ (((p4 ∧ (p2 → (((p4 ∧ (p2 ∧ p5)) ∧ p1) → p4))) → p3) → ((p3 ∧ p5) ∨ p2)))) ∨ (p1 ∨ (p2 ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_130473113891958572986103723823 : (((p5 ∨ (((((True ∧ (p2 → (p3 → (False ∧ p5)))) ∧ p5) ∨ p1) ∨ p2) ∨ (p4 ∨ True))) ∨ ((p2 ∧ False) ∧ p2)) ∧ ((p5 ∨ True) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811237950563906998619565173557 : (((p5 → (p5 ∧ ((p5 → ((((p2 ∧ p3) ∧ p1) → (p3 ∧ (p2 → (p5 ∧ p2)))) ∧ (((True ∧ p5) ∧ False) ∨ True))) → (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323243876976702025295410597887 : (p5 ∨ (((p1 ∧ p5) ∨ (((p4 ∧ ((p4 ∧ (True → ((p3 ∨ p2) → p5))) ∧ p2)) ∨ p3) → ((p1 ∨ True) ∧ (p4 → p1)))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778684994471743780316176256997 : (((p1 ∨ (p2 ∨ (p1 → (((True ∧ (p3 ∨ (p4 → True))) ∧ p3) → (p3 → (((p5 → False) ∧ (p5 ∧ p3)) ∨ ((p4 ∧ False) ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241285768778936096295037359074 : ((False → True) ∧ (((p2 ∧ (True → ((p3 ∨ p4) ∧ p4))) → (False ∨ ((p4 ∨ p1) ∨ (p4 ∨ ((False → (p5 ∧ p3)) ∧ p1))))) ∨ (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604262225681742647533309665212 : ((((True → ((p1 → (False → ((((p2 ∨ True) ∧ ((True ∧ ((p3 → p3) ∨ p5)) ∧ True)) ∨ (p3 ∨ p4)) → (False ∨ p3)))) → p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157596126865653732888419396602 : (((p5 ∨ (p3 → (((p1 ∨ p1) ∨ p5) ∧ (p2 ∧ (p1 ∧ ((False ∧ p2) ∧ True)))))) → (p4 ∧ p4)) ∨ ((p5 → (p1 ∧ (True ∨ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124480461373538615956103988086 : (((((True ∧ False) ∨ (p4 → True)) ∧ p5) ∧ (((p1 ∧ (False ∨ (p5 → False))) → p1) → ((p4 ∧ (p2 ∨ p3)) ∧ (True ∧ False)))) → (p1 ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∧ (False ∨ (p5 → False))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h10
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307607194701480516094472778282 : (p1 ∨ (p1 → ((((p2 ∧ ((p4 ∨ p5) → True)) ∧ p4) → (((((p3 ∨ p4) → p3) ∨ False) ∧ (True ∨ (p4 ∨ (p2 → True)))) ∨ p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778937415530630284195921047037 : (((p1 ∨ (p2 → ((p4 ∧ ((((p4 ∨ (p2 ∧ ((p4 → p1) ∧ p1))) → ((True → (False ∨ False)) ∨ True)) ∧ p1) → p2)) → (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186553906148179810545442220475 : ((((p1 → p4) ∨ (p5 → (p3 → (p2 ∨ p1)))) ∨ (p5 → p1)) → ((p1 ∧ (((False ∨ p1) ∨ ((p4 → p3) ∨ (p5 → p2))) ∧ p5)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258653657776599316069363468159 : ((p5 ∨ p5) → (((((((False → p5) ∧ p5) → (p2 ∨ p1)) → (p2 ∨ p4)) ∨ (p3 → ((True ∨ (p2 → p2)) → p5))) ∧ False) ∨ (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322305381456309188387042754889 : (p5 ∨ (((p2 ∧ (p1 ∧ (((((p3 → True) ∧ ((((p1 → p3) ∧ p3) ∧ p1) ∨ (p5 ∨ p4))) → p4) ∨ (p4 ∧ False)) → p4))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245219845620236310518714419841 : ((p2 ∧ p1) ∨ ((((p5 ∧ False) ∧ (((False → (p2 ∨ ((p1 ∨ p2) ∧ p4))) ∧ (p3 → p1)) ∧ (p1 → ((True → p1) → p1)))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717811329246154472341892313112 : ((((((p3 → False) → p3) ∧ p3) ∨ ((p4 ∧ (((((((p1 → p2) ∨ False) ∨ p5) ∨ (p2 ∨ p2)) → p5) ∧ False) ∧ p3)) ∧ (False → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256993334415451093066443841718 : ((p1 ∨ p5) → (p3 → ((((True → (p2 ∧ False)) → ((False ∧ (p1 ∧ (True ∧ p5))) ∨ ((False ∨ p1) ∧ p2))) ∧ p1) ∨ ((p2 → p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62660304527182145291261771479 : ((p4 ∧ (((((p3 ∨ (p2 ∧ p4)) → ((((p2 ∨ p1) ∧ (p3 ∧ (p4 ∧ p2))) ∨ p5) ∧ p3)) ∨ True) → ((p5 ∨ False) → p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306334874099180093111438144820 : (p1 ∨ ((p3 ∨ True) ∧ ((p5 ∧ (p5 ∨ False)) ∨ ((p1 ∨ ((p4 ∧ p1) ∨ True)) ∨ (p2 → ((p1 → ((p5 → False) → (p5 ∧ False))) ∧ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67388601126461790390829564126 : ((p1 → (((p2 → p2) → (((False → (False → ((((p4 → p3) → p5) ∨ p2) ∨ (((True → p5) ∨ p2) ∧ False)))) ∧ p4) ∧ p3)) → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678538446789380956709110108901 : (((((p3 ∧ (p4 ∧ p5)) ∨ (((p2 ∨ p3) → (p1 ∨ ((p2 ∧ p1) ∧ p4))) ∧ ((p1 ∧ True) → True))) ∨ (False ∨ ((p5 ∧ p1) → p1))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208718363548120375329926927992 : ((p1 ∧ ((p4 ∧ (p5 ∧ p5)) ∨ True)) → (((p3 → False) ∨ (((False ∨ (p5 ∨ p3)) ∧ (p3 → p2)) ∨ (p2 → p2))) ∧ ((p2 ∨ True) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h20



