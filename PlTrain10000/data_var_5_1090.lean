variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300902381846083438782897393396 : (False ∨ (((True → (p3 → (p4 ∨ ((p5 ∨ p3) ∨ ((False ∧ p5) ∨ p4))))) → p3) → ((p3 ∧ ((True ∨ p3) ∧ p3)) → ((True → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197951757785132986241704600576 : (((p2 ∧ p5) ∧ (((p5 ∨ p1) ∧ p3) → p4)) ∨ ((((p4 → p1) → (p2 ∨ (p1 ∧ (p5 → p5)))) → ((p1 ∧ p4) ∨ (p3 → True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783794756919462871298382061479 : (((p3 ∨ (((p2 ∨ True) ∧ (p4 ∨ p5)) ∨ (p4 → ((p2 → ((((((p4 ∧ p5) → p4) ∨ p3) → (p2 ∧ False)) ∧ True) → False)) ∧ True)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 ∧ p5) → p4) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h6
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157690859432145072857272904398 : (((p3 → (((p2 ∧ ((True ∧ (p1 ∨ (p1 → p3))) → False)) ∨ p2) ∨ p3)) ∨ (True ∨ (p3 → p3))) ∨ (((p3 ∨ False) ∨ True) ∧ (p3 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54540416327797296642144455290 : ((((p1 → True) → (p1 ∨ (p3 ∨ (p2 ∨ p4)))) ∨ (False → ((((p3 ∧ p2) ∧ True) → p1) ∧ (False ∨ (p3 → ((False → p1) ∧ p3)))))) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708305000774146716568318553331 : ((((((p1 ∧ (p5 ∨ (False → p3))) ∧ p4) ∧ p4) → (((((True ∧ p4) ∧ True) → False) ∧ (p3 ∨ ((p1 ∨ p4) → (False ∧ False)))) ∨ True)) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112079708845407139813859176819 : ((((p4 ∧ p2) ∨ ((False → ((p4 ∨ True) ∧ p2)) ∧ ((True ∧ (True ∧ ((False ∨ p3) → True))) → (p4 ∨ (p2 ∧ False))))) ∨ p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625786487510344267758432183283 : ((((p1 → (p4 ∧ ((p2 → ((((p1 ∨ p2) → p1) → p5) ∨ p3)) ∨ (p2 ∨ ((((p5 ∧ (p5 ∨ p4)) ∧ p3) → p1) → p3))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217817838945826114797842624902 : (((p3 ∨ (True ∧ True)) → False) → ((((p4 ∨ (True → ((p4 ∨ False) → p2))) ∧ False) ∨ (p4 → (False ∧ p1))) ∧ ((p5 ∧ p5) → (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622509183002925472447751243203 : ((((p3 ∧ (p5 ∨ ((((((True ∨ True) ∨ (p1 ∨ p3)) → ((True ∨ p2) ∨ p2)) ∧ p2) → p1) → (((True ∨ p2) ∨ p4) ∧ p2)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316369245092685097747590672774 : (p3 ∨ (False ∨ ((p3 ∨ ((((p3 ∧ (True → True)) → (p1 ∨ p1)) ∨ False) → ((p3 → p5) → ((p4 ∨ p2) ∨ ((p2 ∧ p1) → True))))) ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149007493762430399005405158530 : ((((p2 ∨ p3) ∧ p3) ∨ (((p3 → (((False → False) ∨ (p4 → (True ∧ p2))) ∨ True)) ∧ p4) ∧ (p1 ∨ p1))) ∨ ((False ∨ (p2 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42229903083339042322513260334 : (((False ∧ (((p1 ∨ True) ∧ ((p1 → ((p1 ∨ p4) ∧ p5)) ∧ True)) ∨ ((False ∧ ((((p3 ∨ p4) ∨ p3) → False) ∧ p1)) ∧ p3))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141197367662016685144326680777 : ((((p5 ∧ True) ∨ (p1 → (p4 → p2))) ∨ (p2 ∨ (((False ∧ p4) → (p2 → (p4 → p3))) → ((False ∧ p1) → True)))) → (p2 ∨ (p3 → p3))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161878405218572215450537463915 : ((False → ((p5 ∨ (((((p2 → True) ∧ p3) ∧ False) → p3) ∧ True)) ∨ (p1 ∧ (p1 ∨ (False → p3))))) → ((True → ((p3 ∧ p4) ∧ p1)) → p4)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762943122875977670603362920919 : (((p3 ∧ ((True ∨ (False ∨ (True ∧ p3))) ∧ (True ∧ ((False → (p3 → (((p2 → p3) ∧ ((False ∧ p5) ∨ p5)) ∨ (p1 → p1)))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157894402423067106759269841840 : (((p4 → ((False ∧ (True ∧ p1)) ∨ ((p5 ∧ p5) ∧ p1))) ∨ (True ∨ ((p4 ∨ (p1 → p3)) → p5))) ∨ (False → (p1 → ((p3 ∧ p1) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135293615555514145457532170730 : (((((p1 ∨ (True ∧ (p5 ∨ (((p5 ∨ p5) ∨ True) → (p5 ∨ p5))))) ∨ (True ∧ p5)) ∧ p4) ∧ (False ∨ (p1 ∨ p1))) ∨ ((True ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252528279403846071704953553981 : ((p5 → p2) ∨ (((p1 → (((p4 → p4) → p3) ∨ (True ∧ ((False ∨ False) → (p5 → p4))))) → p2) ∨ (p4 ∨ (p5 → (False → (p5 ∧ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340929941837217864035574145763 : (p2 → (((p4 ∨ ((False ∧ p4) → (p4 ∧ p3))) → (p1 ∧ ((((p1 ∧ p5) ∧ p1) → (((p1 → (False ∧ p4)) ∧ p3) ∨ p1)) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630934437423969585719963164077 : ((((((True ∧ (p3 → (((((p5 ∨ ((p4 ∨ p2) ∨ False)) ∨ p5) ∧ p5) → p2) ∧ ((p5 ∨ True) ∧ (p1 ∧ True))))) ∧ True) → p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195770261189828892584285115173 : (((True ∧ p4) → (p2 ∨ (True ∨ (True → p1)))) ∧ ((p5 ∨ (p1 ∧ ((p5 ∨ (((p1 ∨ p1) → p5) ∧ p1)) ∨ (p1 ∧ p4)))) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59999281780250744214295547094 : (((False ∨ p4) → (((p4 ∧ ((True → True) → (p1 → p4))) ∧ True) ∧ ((((False → (p1 ∨ (False ∧ p3))) ∨ p4) ∨ True) → (p3 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113465048492147711774698981617 : (((((p5 → p1) ∧ ((p5 → (((False → (p4 ∧ p4)) → False) → (p4 → p3))) ∨ (p3 → (p3 → p5)))) → p2) ∨ (p5 → p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336430019697419680774182985616 : (p1 → ((p2 ∨ ((((p3 → (True ∧ (p4 ∨ (p5 ∨ False)))) → (False ∨ (p5 ∨ (p5 → p5)))) ∨ ((p5 ∧ False) ∧ (p4 ∧ p1))) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113328213970981742191617820585 : ((((p2 → p3) ∧ ((((p5 ∨ p4) → ((p1 ∨ (p2 ∧ p2)) ∨ (False ∧ (p5 ∨ (True → p3))))) → p2) → p1)) ∧ (p4 ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193310186832917114654006737730 : (((True ∨ (False → p4)) ∨ (((p5 ∨ p4) ∧ p3) ∧ p1)) → ((((p4 → p1) ∨ p2) → True) ∧ ((p4 ∧ (p4 ∨ p3)) → ((True → p5) ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742676840189175015468671757381 : ((((p2 → p5) ∨ (((((True → False) ∨ (p1 ∨ (False → p5))) → p1) → ((p4 ∨ (p1 → (False → p1))) → (p1 ∧ (p4 ∧ p3)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249493397182920514115734810323 : ((p5 ∨ p1) ∨ (((p3 ∨ (p5 ∧ p1)) ∨ (p5 → (((p5 ∧ False) → p1) ∨ (p4 ∧ p3)))) ∨ (p4 ∨ ((p5 ∧ True) → (False → (False ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53892617547882152064696750220 : (((False ∧ (p5 ∧ (False ∧ (((p3 ∧ p4) → p4) ∧ p1)))) ∨ ((True → (p2 ∧ (((False → (p1 ∧ p3)) → p4) ∨ p2))) ∨ (p5 → p5))) ∨ False) := by
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
theorem thm_5_vars_40423812060964143289990489236 : ((((((p2 ∧ ((True → (p5 → True)) → p1)) → (p4 ∧ (p3 → (p3 ∨ p4)))) → ((p5 ∨ (p4 → p5)) → (True ∧ False))) ∨ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49179919889764410545486599409 : ((((((p2 ∨ p1) ∨ False) → p2) ∨ (((False → False) ∨ (True → (False ∨ (p1 → p4)))) → ((False ∧ p1) ∨ True))) ∨ ((p4 ∨ True) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629561515652254538182803806658 : ((((((p5 ∨ (((p1 ∧ ((True → ((True ∨ (p5 → False)) ∨ p5)) ∧ (True → p2))) → (True ∧ False)) → p5)) → (p1 ∨ p1)) ∨ p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55570626974248277357087190541 : (((True ∨ ((p4 ∨ p2) → (p5 ∨ True))) → (False ∧ ((p4 → p5) ∨ ((((p1 ∨ p4) ∨ ((p5 → p4) → p3)) ∧ (True ∨ p4)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647837604895925212503527544402 : (((((((((p5 ∨ p2) → ((p3 ∨ ((False → p5) → p2)) ∨ (((False ∧ p3) → p4) → p5))) → p3) → p2) ∨ p4) ∧ p1) ∧ (p3 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45981277504953199775297924083 : (((((((p4 → ((p3 ∨ p4) ∧ (((p2 → p3) ∨ (False ∧ ((True ∧ p1) ∨ True))) ∨ p5))) ∨ p4) ∨ p5) ∨ p1) ∧ p5) ∧ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201133475300405307524556148027 : ((False → ((False ∨ ((p5 ∨ p5) ∧ p1)) ∧ True)) → (p1 → (((True → (False ∧ p5)) ∨ (((((p5 ∧ p2) ∧ False) ∨ False) ∧ p2) → True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262167288126649071800402995331 : (True ∧ (((p4 ∧ (((p5 ∧ p2) ∨ (p3 ∧ (((p2 ∧ (p4 ∨ False)) → (p1 → p2)) ∨ p2))) ∨ (p1 → ((p1 → p3) ∧ False)))) ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119202790713080756690880698293 : ((p2 → (((p1 ∨ (p3 ∨ ((p1 → False) ∨ (p1 → (p2 ∨ p4))))) → (p5 → p1)) ∧ (p1 ∧ ((p1 ∧ (p2 ∨ p4)) ∧ p1)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339760504166816527005265793940 : (p1 → (p4 ∨ ((p3 → True) → (((p5 ∨ (p2 → p2)) → (p3 ∨ (((p3 ∨ False) ∨ p3) ∧ (p5 ∧ (p1 ∧ p1))))) ∨ (p3 → (False → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321473926121439696276326973386 : (p4 ∨ (p1 → (((((p2 → ((p1 ∨ (p1 ∧ p3)) → p3)) ∧ ((p5 → p1) → ((p3 ∧ (p4 → p3)) ∨ p3))) → (False ∧ p3)) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_117173182255175512983474858551 : ((True ∧ (((False → False) → ((p5 ∨ ((((False ∧ (p5 ∧ p5)) → p2) → True) → p4)) ∧ ((p1 → True) ∨ (False ∨ p1)))) → False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405092289894473904849620571546 : ((((((p1 ∨ (p4 ∧ ((p1 ∧ ((((p2 ∨ False) ∧ p1) ∧ (False → False)) → p2)) ∨ p1))) ∨ ((p2 ∧ (False ∨ False)) → p4)) → p2) → p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p4 ∧ ((p1 ∧ ((((p2 ∨ False) ∧ p1) ∧ (False → False)) → p2)) ∨ p1))) ∨ ((p2 ∧ (False ∨ False)) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135768526780883820055769071437 : (((((p2 ∧ ((p2 → p3) ∧ ((p4 ∧ True) ∨ p5))) → (True ∧ p3)) ∧ p3) → ((p1 → False) ∨ ((p1 → True) ∨ True))) ∨ (True → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682203433801333197848967666626 : (((((True ∧ (p3 ∨ (True ∨ ((p4 ∨ (True ∨ (p1 → ((p3 ∧ p3) → p1)))) → True)))) → p5) ∧ ((False ∧ (p3 ∨ True)) ∨ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67282574159788451900830860263 : ((p1 → ((((((p2 ∨ ((True ∨ (False ∨ False)) → p4)) ∨ False) ∧ ((((p5 → p4) → (p2 ∧ p1)) → False) ∧ p4)) → p5) ∧ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46664763509233605995350097342 : (((False ∨ (p1 ∧ ((True ∧ (True ∧ (((p2 → True) ∨ p2) ∧ (p5 → (False ∧ ((p2 → p4) → p3)))))) → (True → p3)))) ∧ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807713935745565033091951068934 : (((p4 → (((p2 → p4) → p3) ∨ (((False → p3) → p1) ∨ ((((p2 ∧ (p5 → True)) → (True → (p2 ∨ (True ∨ p3)))) ∨ False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350960520145588417376136074904 : (p4 → (((False → (p5 ∧ (False → (((p3 ∨ (p2 ∧ p5)) ∨ True) ∧ False)))) → ((((p5 ∨ p3) → p3) ∨ p1) ∨ (p4 ∧ True))) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153539306105453852186680104999 : ((True → ((p5 ∧ (p3 ∧ (((p3 ∧ (p2 ∧ p5)) → p2) ∧ p4))) ∨ (p5 → (((p5 ∨ p2) ∧ p5) → p1)))) → (p1 ∨ (True ∨ (False ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751043327995338307671087392473 : (((True ∧ ((p5 ∨ ((False → p3) ∧ p3)) ∧ ((((p5 ∨ ((((p1 ∨ (p3 → False)) → True) ∧ p2) ∨ p1)) → (False ∧ p5)) → p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300817714400485315701898172332 : (False ∨ ((((p3 ∧ ((p1 → p5) ∨ False)) ∨ False) → (p1 ∨ (((p2 ∨ p5) ∧ p3) ∨ p5))) → ((True → (p4 ∧ (p3 ∨ (True → p4)))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164791268143173017878320569102 : ((((False ∧ ((p1 ∨ False) ∨ False)) ∨ ((p4 ∧ p2) → (p4 ∧ ((p2 → p5) → False)))) ∨ p5) ∨ (p3 → (((True ∧ (p4 → p5)) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218297141823886285261426569038 : (((p4 ∨ p2) ∨ (p1 ∨ True)) → ((((p2 → ((((p5 → True) → (p2 → (p4 ∧ p2))) ∧ (p4 ∧ False)) ∧ False)) ∧ p4) → p5) ∨ (False → p3))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709416753449786432390896662309 : ((((p1 ∧ ((False → p1) ∨ ((p4 → p5) ∧ p4))) → ((p5 ∨ (p4 → ((((((p3 ∨ p4) ∨ p5) → p3) ∨ False) ∨ p4) ∨ False))) ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656403282895443296835334270866 : ((((((((p5 ∧ p2) ∧ (False ∧ p4)) ∧ p3) ∨ (False ∨ p3)) ∧ ((p2 → p1) ∧ (((False → p5) ∧ p3) ∧ (p5 → p2)))) ∨ (True ∨ p2)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_50972166148626665080447729133 : ((((True ∨ ((True → p5) ∨ p1)) → ((((p2 ∨ (p2 ∨ False)) → False) ∧ (p4 ∨ p4)) ∨ True)) ∧ (((p4 ∨ False) ∨ (True ∧ p1)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53660709022546162769362367783 : ((((p2 → True) ∧ (((True ∧ p1) ∧ p5) → (p2 ∨ p5))) ∧ (p2 ∧ (p3 ∨ ((p2 → (((True → p5) ∧ (p3 → True)) ∨ p5)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37544480066706109496136267515 : ((((p5 ∧ ((p5 ∨ p1) → (((False ∧ (p3 ∨ (True ∧ (p3 ∧ (False → ((True ∨ True) → p5)))))) ∧ (p1 ∧ p4)) ∧ False))) ∨ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676664679283838275366651478786 : ((((p4 ∧ (((True → p4) ∨ False) ∨ (((((p3 ∨ p1) ∨ False) → p2) ∨ (True ∨ p5)) ∨ (p5 ∨ True)))) ∧ (False ∧ ((p3 → p2) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39271473461687439916757102184 : (((False ∧ (p1 → ((False ∨ ((p1 → p1) ∨ p5)) ∧ (p3 → ((p5 ∨ (p2 ∨ (p5 → (((False ∨ p2) ∧ False) ∧ False)))) ∧ p1))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778261273009107427849923389083 : (((p1 ∨ (True ∧ ((p4 ∨ ((True ∨ ((p2 ∨ p5) ∨ (p2 ∧ (p3 ∧ (True ∧ ((p4 ∨ True) ∨ p4)))))) ∧ ((p3 ∧ p1) ∧ p4))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5802950236230655539427887652 : (((((True → (((p5 ∧ (True → p4)) ∨ p3) → ((True ∨ p3) → (p4 → False)))) ∧ (p4 ∨ (p5 ∨ p2))) ∨ ((False → p2) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65955003417711373935470077022 : ((p4 ∨ (p3 ∨ (p2 ∨ ((p4 ∧ (p4 ∨ False)) ∨ (False → ((p1 ∨ True) → ((p3 → (p4 → (p4 → (p2 ∧ (p4 ∨ p4))))) ∧ p2))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305919092794980420769228603556 : (p1 ∨ (((p1 ∧ p5) → ((p5 → p5) ∨ p4)) → (p4 ∨ (((False → ((((p5 ∨ p3) → p2) → False) ∨ (p4 → p4))) → p3) ∨ (p5 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68397057935604543935847742233 : ((p3 → ((p2 ∧ (p1 ∨ p5)) ∨ (((True ∧ ((True ∧ (p3 ∨ p1)) ∧ (((p3 → p3) ∨ (True → (p4 → True))) → p4))) → p4) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 → p3) ∨ (True → (p4 → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h10
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : ((p3 → p3) ∨ (True → (p4 → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h18 := h6 h15
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319065066650044887567045787317 : (p4 ∨ ((p5 ∨ (p3 ∨ (((p2 ∨ ((p2 ∨ p2) → p1)) ∨ (p5 ∧ (p5 ∨ (p4 ∧ p3)))) → (True ∧ p5)))) ∨ (((p3 ∨ True) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_166584567715713404361423440778 : ((True → (((p2 ∨ (p2 → (p5 → False))) ∧ p4) → (((p3 → p5) ∧ (p5 ∨ p1)) ∨ p4))) ∨ ((((p2 ∧ (p3 ∧ False)) ∨ p2) → True) ∧ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262273149166785064849447182652 : (True ∧ (((((p5 ∧ ((p4 → False) → (p5 → p4))) ∧ p3) ∨ (p2 ∧ (p3 ∨ (p2 → (p4 ∨ p1))))) ∨ ((p4 ∨ p3) → (p4 ∨ p3))) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91139125161837311186761145011 : (((p4 → p4) ∧ (((((p5 ∧ p3) → (False → p2)) → (((((p4 → True) ∧ p5) → p2) ∨ (True ∧ True)) ∨ False)) → False) ∧ (p1 ∧ p3))) → p5) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (((p5 ∧ p3) → (False → p2)) → (((((p4 → True) ∧ p5) → p2) ∨ (True ∧ True)) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349032784090441881038961166003 : (p3 → (p5 ∨ ((((True → p2) → p4) ∨ (((p5 ∧ True) ∨ (((((p1 → False) ∧ p2) ∨ p2) ∧ p3) ∨ p3)) → ((False → p3) → p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681161738546360709248638629987 : ((((p1 ∧ (p4 → (((p5 ∨ ((False ∨ True) ∨ (p2 ∨ p3))) ∧ (False ∧ (False ∧ p4))) ∨ (p5 → p1)))) → (((p3 → p4) ∨ True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715191890458677523548320108711 : ((((False → ((p5 ∧ (p3 ∧ p1)) ∧ p5)) → ((((False ∨ False) → False) → p4) → ((p3 → (True ∨ p1)) ∧ (((p4 → p5) → p3) ∨ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ False) → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593698794846293088316915117658 : ((((((p1 ∧ ((p2 → (p5 ∨ p5)) ∧ ((p2 ∧ True) ∧ (p4 ∧ p1)))) → (False → (True ∧ p3))) ∧ (((p2 ∨ p3) → p5) ∨ p2)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228165645617395159548829001676 : ((p5 ∧ (False ∧ False)) ∨ (((((p2 → (True → True)) → (True ∨ (False ∨ p2))) ∧ (p1 → (True → p3))) → (False ∨ (p1 ∨ True))) ∨ (True → p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232728922647956427487903034325 : ((p1 ∧ (True → p3)) → (p3 → (((((((p2 → p4) ∨ p5) ∧ (p4 ∨ (False → (True ∧ p1)))) → (p2 ∨ p2)) → (p5 → True)) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40404878842287975719484190503 : ((((((((p3 ∧ (p4 ∨ ((((True ∧ p3) ∨ p1) ∧ (False ∨ p3)) ∧ p1))) → False) ∧ True) ∨ p3) → (p1 ∧ (True → p4))) ∨ True) ∨ p4) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230635799996852913279785782155 : (((p2 → p5) ∧ p2) → (((p2 → ((((p3 → p2) → (p2 → p4)) ∧ (p3 → (p1 → (p1 ∧ False)))) ∨ p2)) ∨ (False → p2)) ∨ (p1 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152581848923058441916500542463 : (((p5 → (p4 ∧ True)) → ((((((p2 ∧ p3) ∧ p3) → p2) ∨ p3) → False) ∧ ((p2 → p4) → (p3 → p2)))) → (((p1 → p3) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160702584169656708055720755039 : (((((p3 ∨ (p1 → (p3 ∨ p3))) → False) ∨ False) ∨ (p3 → ((p2 ∧ (p4 → (p3 → True))) → p4))) → (p2 → (p3 → (p4 ∨ (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p3 ∨ (p1 → (p3 ∨ p3))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∧ (p4 → (p3 → True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264579237934608742866315212550 : (True ∧ ((False ∨ (p1 ∨ p4)) ∨ (p4 ∨ (p2 → (((p4 ∧ ((p2 ∧ p2) ∧ p2)) → p2) → (p1 → (p3 ∨ (((p2 → p3) ∨ p2) → p1)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867572307848296032761549687980 : (((((p4 ∧ False) ∨ ((p5 → (((p2 ∧ (p1 ∨ True)) ∨ ((p1 → (((p5 → p5) ∧ True) ∨ p5)) ∨ True)) ∧ True)) ∨ (True → p2))) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ False) ∨ ((p5 → (((p2 ∧ (p1 ∨ True)) ∨ ((p1 → (((p5 → p5) ∧ True) ∨ p5)) ∨ True)) ∧ True)) ∨ (True → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137968990332646587231016439141 : ((p5 ∨ ((p3 ∧ ((p4 → True) ∨ (((((p4 → p4) → True) ∧ p2) ∧ p5) ∨ False))) ∨ (((p2 ∧ False) ∨ p1) ∧ p2))) ∨ ((p5 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65827498849682256774804678073 : ((p4 ∨ ((p4 → ((False ∧ p3) ∨ p2)) ∧ (((False → p2) ∨ ((True ∨ p5) → ((p1 → (p4 ∧ True)) → (True ∨ True)))) → (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303827514743162901407859877865 : (p1 ∨ (((((False ∨ (p4 ∧ p2)) ∧ ((p1 ∧ True) ∧ (True → True))) ∧ (p1 → (((True → p3) → p5) ∨ (p1 ∨ p3)))) ∧ (p5 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198724601673098360413834896476 : ((p5 ∨ ((p5 → False) → (p2 ∨ (p3 ∨ p2)))) ∨ (((p3 ∧ p3) ∨ ((((p4 ∧ True) ∨ (p5 ∧ p3)) → (True → p5)) ∨ (False ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234533960851275659256502971974 : ((p2 → (p5 → p3)) → (p4 → ((p3 ∨ True) → ((p1 ∨ p3) ∨ (True ∨ (p5 ∨ ((((True → (p4 ∨ (p3 ∧ False))) → p3) ∨ True) → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48078773522153031736901327869 : (((((((True ∧ False) → p1) ∨ p2) → True) ∨ (p5 → ((((p2 ∨ (True ∨ p2)) → p3) ∧ (p2 ∨ p4)) → (p1 ∧ True)))) → (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114428771168831979410137147359 : (((p4 ∧ (((((p5 ∧ (False → True)) ∧ p3) ∨ p4) ∧ (p4 ∨ (True ∧ (p2 ∧ p3)))) ∧ p3)) ∨ (((p3 ∨ p2) → p2) → True)) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824615285826160522995850135209 : (((((p4 → (p5 ∧ True)) ∧ ((((((True ∨ p3) ∧ p2) ∨ p2) ∧ p5) ∨ (((p4 ∧ True) → p1) ∧ True)) → ((p4 ∨ True) → p2))) ∧ p4) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215810783150392908313284052755 : ((p1 ∨ (p5 → (p4 ∧ p2))) ∨ ((p1 ∧ (((True ∨ p2) → p5) ∨ p4)) ∨ (False → (p1 ∨ ((p4 ∨ ((p4 → (p4 ∧ p4)) ∨ p2)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206466756317255137419770567742 : ((p4 ∨ (p3 ∨ (p3 ∨ (False ∧ p3)))) ∨ (((False ∧ p5) ∧ (p1 → (p4 ∨ ((p5 ∨ ((p4 ∨ p4) → p3)) ∨ p1)))) → ((p4 ∨ p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708654856612879417691889698539 : (((((((p4 ∧ p1) ∨ (p3 ∧ p5)) ∧ p1) → p1) → (((False ∨ (True ∨ (p1 ∧ p3))) ∧ ((p1 → p4) ∨ (p5 ∨ (p4 ∧ p4)))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_112874676098499538782165273436 : ((((True ∨ (p2 ∧ True)) → ((p1 → (p3 ∨ p4)) ∧ (((p4 ∨ ((p2 ∧ p5) ∧ p3)) ∧ p1) ∨ (p2 ∨ (p3 ∧ False))))) → p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111936537127581812331607629981 : (((((p5 ∧ p5) ∨ ((((p1 ∧ p1) ∧ p4) → p3) ∧ True)) ∨ ((p2 → (p1 → False)) → (p5 ∨ ((False → p4) → p3)))) ∨ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113083673860291278779194475373 : (((p4 ∨ ((True → p3) ∧ ((p5 → (((p3 ∧ False) ∧ p2) ∨ (p4 ∧ p1))) → (((p5 → p5) ∨ (p3 ∨ p5)) → p4)))) → p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4293598766358103353331242830 : (True → (((((False → p2) ∧ True) ∨ False) ∨ p1) → ((p2 → ((False ∧ (True ∨ p2)) ∧ (p2 ∨ p4))) → (p2 ∨ (p4 → (True → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118482116454508213856225140210 : ((p3 ∨ (((True → (p1 ∧ (p3 → (p4 ∨ (True → ((True → (((p2 → p3) ∨ True) ∨ p1)) ∧ p1)))))) ∨ p4) → (p3 ∨ False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45279889145171029662721036965 : (((p2 ∧ ((False ∨ ((((p2 ∨ p2) ∨ p2) → ((((p4 ∨ p5) ∨ p3) → p4) ∨ (p1 → p2))) ∧ p4)) ∨ ((p5 → p5) ∧ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728200471901506629186923101886 : ((((True → (p3 ∧ p1)) ∨ (((False ∨ (((p3 → p3) → (p4 ∧ ((p4 ∧ p4) ∨ p1))) ∧ (p4 ∨ False))) → p5) ∨ ((p3 → True) → True))) ∨ False) ∧ True) := by
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



