variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231465017762263231437574228258 : (((p2 → p5) ∨ p5) → ((((p1 → p3) → p3) ∨ p1) ∨ (p4 → ((p4 ∧ True) ∨ ((p3 → ((p4 ∨ (False ∨ p1)) → p1)) ∨ (True → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191287063138084564854482350029 : (((p5 ∨ p1) ∧ (((False ∧ (p5 ∧ p4)) ∧ p4) ∨ p3)) ∨ ((True ∨ ((((((False → False) ∨ True) ∧ False) ∨ p5) ∨ p1) ∨ (p1 ∧ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806289127356404346395328309701 : (((p4 → (((((p3 ∨ (p2 ∨ p1)) → p4) → p3) ∨ ((p5 ∧ ((p4 → (((p4 → False) ∧ p5) ∨ False)) ∨ False)) → (p1 ∧ p5))) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347931283398997298704493752501 : (p3 → ((p1 ∨ True) ∧ (True → (((p2 ∧ (p5 ∨ p3)) → (((p1 ∨ p1) ∨ (p2 ∧ (p4 → (p3 ∧ ((p1 ∨ p3) ∨ p4))))) ∨ p5)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135636566416679081794796472406 : ((((((p1 ∧ ((p4 → p4) ∧ p1)) ∧ p2) ∧ (p2 ∨ ((p2 ∧ False) ∨ p2))) → False) → (p3 ∧ ((False ∧ p1) → p4))) ∨ (True ∨ (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321631773836630204255642992361 : (p4 ∨ (p3 → ((p4 ∧ p4) → (((False ∧ False) ∧ (True → (False ∨ p2))) ∨ (((False ∧ p1) ∧ (((p2 ∧ p3) ∧ True) ∨ True)) → (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181637341163600237713715867833 : ((p3 → (((p3 ∨ False) → ((p3 ∧ (p1 → (True → p5))) ∧ p4)) ∨ p2)) → ((((p5 → (p3 ∧ (p2 ∨ p2))) ∧ p2) ∧ (True → p1)) → p1)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119082875558017479145220369273 : ((p1 → ((p5 ∨ (p1 ∧ (False ∧ (((True → p1) ∧ (p5 ∧ ((p3 → p4) → p5))) ∧ False)))) ∨ (((p3 → True) ∧ True) ∨ p2))) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148131346940973212359870628567 : ((((p2 ∨ p5) ∨ ((p3 ∨ ((p2 → p1) → (p4 ∧ (True ∧ (p1 ∧ p1))))) → (p4 → p5))) → (p3 ∧ False)) ∨ ((p3 ∧ (p1 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68308865482310545838920213069 : ((p3 → ((((False ∨ p4) ∨ p2) ∨ (((p2 ∧ (p4 ∧ (p2 ∧ p2))) ∨ (p2 ∧ p4)) → (False ∧ p1))) ∨ (p3 ∨ ((False ∧ True) ∨ p2)))) ∨ p1) := by
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
theorem thm_5_vars_249977848761506711353412298155 : ((True → p2) ∨ ((True ∧ (((((p1 → False) ∧ p4) ∧ ((False → p4) ∧ (p5 ∨ True))) ∧ p5) ∨ p4)) ∨ ((p3 → (p2 ∨ p5)) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_562197554109696242151634989888 : (((p5 ∨ (((True → (False ∧ p2)) ∧ ((p1 ∧ (p1 → ((((p5 ∨ False) ∨ True) → (p2 ∨ (p2 ∨ p4))) ∧ (p5 → False)))) → p4)) → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42331467901365559278367711643 : (((p3 ∧ ((p3 ∨ ((p4 ∨ (((p3 ∨ (((False ∧ p1) ∨ p5) → p1)) → ((True ∧ p2) ∨ (p2 ∨ False))) → False)) ∨ p5)) ∧ p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233613484256767959578417720698 : ((p2 ∨ (p3 ∧ True)) → (((p1 ∧ (p5 → ((((((True → p1) → p1) ∨ (p5 ∧ False)) ∧ (False → p3)) ∧ True) ∨ (p1 ∨ p3)))) → p4) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63019419741919598216628879356 : ((p4 ∧ (p4 → (((((p2 ∧ p3) ∧ p3) → (False ∨ ((((p1 ∨ p3) → (p5 ∧ p1)) ∧ (p2 → (p3 ∨ p1))) ∨ p4))) ∧ False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223615748624037325031235249267 : ((p1 ∨ (p3 ∨ True)) ∧ ((p2 ∨ ((((p5 ∨ p5) ∨ (p2 → p1)) ∧ p3) ∨ (p1 → (False → (p2 ∨ (p4 ∧ (True → p3))))))) ∨ (True ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243417005835045342803300723187 : ((p5 → True) ∧ (((p2 ∨ (p4 ∨ (p1 ∧ (p3 → (True → ((False ∨ (p1 ∨ (True → p4))) ∧ False)))))) ∨ p1) ∨ ((p2 ∧ p3) → (p5 → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_441927497766379292998628797408 : ((((((False ∨ (((True → (p2 ∧ p2)) ∨ (False ∧ True)) ∧ ((True ∨ (p3 ∧ (p2 → False))) ∨ True))) → False) ∧ p3) ∨ (False → (False ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157087599110742635013042880922 : (((p5 ∨ (((p2 → p1) ∧ (((p2 → p1) → p2) ∨ p1)) → ((p2 ∧ (p2 ∨ p5)) → p5))) ∨ p2) ∨ (((p4 → p5) → True) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45552697343290808565259064000 : (((p2 ∨ (((p4 → ((((((p1 → p4) ∨ p3) → (p4 ∧ p5)) ∧ True) → p5) ∨ p3)) → ((p2 ∨ False) → p4)) ∨ (False ∨ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111426632381433853635227758608 : (((p4 ∨ ((p5 ∨ ((p5 ∨ (((p4 ∧ p2) ∨ p1) → (p4 → (((p2 ∨ p1) ∧ False) ∧ True)))) ∧ True)) ∧ (False → p1))) ∧ False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655062104389469685889607231465 : (((((p3 ∧ (((p1 → (p3 → (p3 ∧ p4))) ∧ (True → p4)) ∧ ((True → (True ∨ (False → (p1 ∨ p2)))) ∨ False))) → p2) ∨ (p1 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60752853251003384253515440400 : ((True ∧ ((p5 ∨ (p5 ∨ True)) → (p1 ∨ (p4 → ((p2 ∧ ((p3 ∨ p2) ∨ ((True ∧ (p4 ∧ p5)) → (False ∨ (p5 → True))))) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304211939488008577829253220959 : (p1 ∨ (((((p4 ∧ (((((p5 ∨ p1) ∧ p1) ∧ (False → ((True → p4) → p1))) → p4) ∨ ((p2 ∧ p4) ∨ p1))) ∧ True) ∨ True) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ (((((p5 ∨ p1) ∧ p1) ∧ (False → ((True → p4) → p1))) → p4) ∨ ((p2 ∧ p4) ∨ p1))) ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326316502917146120134313725790 : (p5 ∨ (p4 → ((p3 → p2) → (((p4 → (p4 ∧ (p1 → True))) ∧ ((p5 ∨ p2) → (p3 → (p3 ∨ p1)))) → ((False ∨ True) ∧ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305422345537500243397131845320 : (p1 ∨ ((p1 → (p3 ∨ ((p5 → ((p3 ∧ False) ∧ (False ∧ (True ∧ (True ∨ p3))))) → p5))) ∨ (p2 → (p2 → (((True ∨ p3) ∨ p3) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317719532057653081984335563393 : (p4 ∨ ((((False ∨ (p1 ∨ ((p5 → p1) ∧ False))) → (((p5 ∨ ((p4 ∨ (True → (p3 ∧ p1))) ∧ True)) → False) ∧ p4)) → (p3 → p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231098236636683775202877173978 : (((False ∨ p3) ∨ p3) → (p4 → (p1 ∨ ((p2 ∨ (p4 → (((p2 ∧ (((p1 ∨ p4) ∨ p2) ∧ False)) ∨ ((p1 → False) ∧ True)) ∧ True))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256641597702413710353924827147 : ((p1 ∨ False) → ((p3 ∨ (((((False ∨ ((False ∨ False) ∨ p2)) ∨ True) → p4) → p3) ∨ (False → ((p1 ∧ p3) → (p4 ∧ (p5 → p1)))))) ∨ p5)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326302407446954574741001639445 : (p5 ∨ (p4 → ((((p2 → (p5 ∧ p1)) → ((p3 ∧ p5) ∨ (p3 → p2))) ∨ True) ∨ (p4 ∨ (p1 ∧ (False ∧ (p4 ∧ ((p3 ∧ p2) → p2)))))))) := by
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
theorem thm_5_vars_191796259376440866020087143458 : ((p2 ∨ (((p5 ∨ (False → False)) → (False ∨ p3)) ∨ False)) ∨ ((True ∧ False) → (p1 ∧ ((True → (((True ∧ p4) → p5) → p2)) → (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51703142970904283066504058546 : (((((p4 ∧ (False → (((p2 ∧ p2) → True) ∧ p4))) ∧ True) → (p3 ∧ (False ∨ p2))) ∧ ((p4 ∧ p1) ∨ ((True ∨ (p4 → p2)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160366185828514320542171947980 : (((((p2 ∨ ((p1 ∨ False) ∧ False)) → (p2 → (False ∧ p5))) ∨ (p2 ∧ p4)) ∧ ((p1 ∨ p4) ∧ p1)) → ((((p2 ∧ p2) ∨ p2) ∨ p2) ∨ p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327195654455417383719851758287 : (True → ((p4 ∨ (((((((p1 ∧ p1) → ((True → False) → p5)) ∧ p4) ∧ (p1 ∨ p5)) → (p4 → (p5 ∧ p5))) → p1) ∨ (False ∨ True))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51242606443308105810053147122 : ((((p3 ∨ (p3 ∨ p3)) ∨ (p4 → (False ∨ (((p4 ∧ True) ∨ p3) ∧ (p1 ∨ (p2 ∨ p2)))))) ∨ (((p2 ∧ (False ∧ p5)) → p4) ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_113491668134532158391263292818 : ((((((p3 → ((p4 ∧ (p4 ∨ (False ∨ p4))) ∨ (p4 ∧ p2))) ∨ (p5 ∧ False)) ∨ p2) ∧ ((p4 → False) ∧ p4)) ∨ (True → True)) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134999144922939209433307243184 : (((p2 ∧ (p3 → ((((p1 → True) → ((False ∧ p3) ∧ ((p2 → p4) ∧ p2))) ∧ p3) ∧ (True ∧ True)))) ∧ (p5 ∧ True)) ∨ ((p1 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251378939024418290923114889908 : ((p2 → p4) ∨ (((p3 → ((True ∨ False) ∧ ((True → True) → False))) → p1) → ((((p5 ∨ ((p5 ∨ p1) ∧ p2)) ∨ p4) ∨ (p4 → True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172044134913509273634485187737 : (((p1 → (((((False → p4) ∨ False) → False) → p5) → (False ∧ p3))) ∨ (p3 → True)) ∨ (((p4 → (True ∧ ((p3 ∧ False) ∧ p2))) ∨ p3) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57531262444781768964568044630 : (((p5 → (p1 ∨ p2)) ∨ (((True ∨ p2) ∨ ((p2 → ((p3 → p4) → p2)) ∨ p3)) → ((p5 ∧ True) ∧ (((p4 → p4) ∧ p1) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607245174837506289376523144606 : (((((((p3 ∨ (p1 ∧ True)) ∧ True) → ((p2 ∨ (p2 → ((p2 ∧ (p4 ∧ ((p4 ∨ p3) → p3))) → (p3 → True)))) → p2)) ∧ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_213321261779587141953711314893 : (((p1 ∧ (True ∧ False)) ∧ p4) ∨ (((p5 ∨ (p3 ∧ p5)) ∧ (True → (True → (p3 ∨ p5)))) ∨ ((p3 ∨ ((True → (False → p3)) ∨ p4)) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592035401294850527471568495692 : (((((p4 ∧ (((p4 → p1) ∨ (p5 → (p2 ∨ ((((True ∨ p1) ∨ ((p4 ∧ p3) → p1)) ∨ p3) ∨ p5)))) ∧ p1)) ∨ (p3 ∧ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253906939895305950272826612416 : ((p1 ∧ p4) → (((((False ∧ p5) ∨ p2) → (p5 ∧ False)) ∨ ((p1 → ((((False ∨ True) ∧ p1) → True) ∧ p2)) → ((p2 ∨ False) → p5))) ∨ p1)) := by
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
theorem thm_5_vars_619725169347253601860143128745 : (((((True ∨ False) ∧ (((True ∨ p3) → p5) → (((p2 ∨ (((True → p3) ∧ p5) ∨ p4)) ∨ p4) ∨ (True ∨ (p4 ∧ (p5 ∧ False)))))) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114421925507202081018993049713 : ((((p3 → False) → ((p3 → p3) → (p4 → (p2 ∧ (((True ∧ False) ∧ (p5 → p3)) → p4))))) ∨ (p2 → ((p1 → p5) ∧ False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671828640360983492374014052214 : ((((((p2 ∨ p1) → (((p1 ∧ (p2 → p4)) ∧ ((p5 ∨ (p5 → p2)) ∨ False)) ∧ (p1 ∨ (True ∨ True)))) ∧ p4) → ((p1 ∧ p1) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144539716317295047416139165244 : (((((p1 → p4) ∧ ((p1 → ((p2 ∧ (p1 ∧ False)) ∨ p5)) ∨ p4)) ∧ (p1 ∨ (False ∨ p3))) ∨ (True ∨ p1)) ∧ (((p4 → True) ∨ p5) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185502443051082460219966920686 : ((p2 ∨ (((False → False) → False) → ((False ∨ (p2 ∧ p2)) ∨ p1))) ∨ ((p1 ∨ (((False → p5) ∧ ((p5 ∨ (True → False)) → p3)) → p4)) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233673766083553702680399676540 : ((p2 ∨ (True → p4)) → (((p3 → p5) → (((((p5 ∨ False) → (True → (p5 ∧ p1))) → (p5 → ((True ∧ p3) → p1))) ∧ p5) ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_103243601246647436537789018722 : (((p3 ∧ (False ∨ ((p4 ∧ (p4 ∧ p1)) ∨ (p5 ∧ (p5 ∧ ((True → ((p5 ∨ (p1 → p4)) → (False ∨ p5))) ∨ p1)))))) ∨ True) ∧ (True ∨ p4)) := by
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
theorem thm_5_vars_147593379935501121760115538656 : ((((((((p4 ∧ (False ∧ (True → (p4 → p3)))) ∨ False) → p5) → ((p5 → False) ∧ p5)) → p1) ∨ False) → p2) ∨ (True ∨ (False ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266267672048020512098139972624 : (True ∧ (p5 → ((((p4 → p4) → p1) ∧ (False ∧ p1)) ∨ (True → (p2 ∨ (True → (((p2 ∧ (p3 ∧ True)) ∨ p2) ∨ ((True ∨ p3) ∨ p2)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204349481437434975571169205002 : (((False ∨ ((p1 → p3) ∨ False)) ∧ True) ∨ (((p3 ∨ p3) ∨ p4) → ((True → (p1 ∨ (False ∧ ((p5 ∧ (p4 ∨ False)) → (p5 → p5))))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h19
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146901802880507906568450487297 : (((((((p1 ∧ True) → (False ∨ ((p1 ∧ ((True ∧ p3) ∧ True)) ∨ p5))) ∧ (p3 ∧ p2)) ∧ p2) ∧ False) ∧ True) ∨ ((False → (p3 → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249597525841208475974334999099 : ((p5 ∨ p3) ∨ ((p4 → ((((p2 → ((((p2 ∧ p4) → p5) → True) → p3)) ∨ (True ∧ ((p4 ∨ (p4 → p2)) ∨ False))) ∨ True) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231186587362729780168161642800 : (((p2 ∨ p5) ∨ p1) → (p3 → ((p1 ∧ p4) ∨ (((p3 → p5) → p5) → (p1 ∨ ((((p4 → ((True ∧ p3) ∧ True)) → p3) ∧ True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350073012496701891213407152912 : (p4 → (((p1 ∨ ((((p1 ∨ ((((p5 → (p3 ∧ p3)) → p5) ∨ True) → p4)) ∨ ((p1 ∨ p2) ∧ True)) ∨ p5) → p2)) ∨ (p4 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226167533834130219914009221277 : (((p1 ∨ p1) ∨ p4) ∨ (p1 → (p3 → (((False ∨ (p5 ∨ (True ∧ ((p5 ∧ p3) ∨ False)))) ∧ True) ∨ ((p3 ∨ (True → (p5 ∧ False))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618474119614618756968213930363 : (((((((p2 ∧ p4) → p1) → p3) → (((p3 ∨ (((False ∧ p2) ∧ (p3 ∧ True)) ∧ (((p5 ∨ p1) ∨ p1) → p2))) ∨ p3) ∧ p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_337473367250956960675245285477 : (p1 → (((((((((p5 → True) ∨ False) → (p1 ∧ (False ∧ False))) ∧ p4) ∨ p4) ∨ (False → p1)) ∨ p3) ∨ p1) ∧ (p5 ∨ ((p2 → p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315399372510161578677587202573 : (p3 ∨ (((p2 ∧ p4) ∨ p2) ∨ (True → ((p1 ∧ (p4 ∨ ((True ∨ True) ∧ ((p4 ∧ False) ∧ p3)))) ∨ (True ∨ (((False → False) → False) → p2)))))) := by
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
theorem thm_5_vars_264466184958047502686537671166 : (True ∧ ((p5 → ((p1 ∨ p1) → False)) → (((((p3 → (p3 ∧ p2)) → (p5 ∨ (p3 ∨ True))) ∨ True) ∨ (p5 ∧ False)) → ((p5 → p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176659311569761262773462730625 : (((False ∨ ((p1 ∨ p5) ∧ p2)) ∨ ((p3 ∨ p2) → (True ∨ (True → p2)))) ∧ (p4 ∨ (True ∨ ((p3 ∧ ((p4 ∧ p3) ∨ (True ∨ p5))) ∧ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_784776937564562609643775632757 : (((p3 ∨ (True → (((p2 → (p3 ∧ False)) → ((True → (p2 ∨ p1)) ∧ p4)) → (((p5 ∨ True) ∧ (True ∨ ((p4 ∨ p4) ∧ True))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765644936335347099188106206271 : (((p4 ∧ ((p2 ∨ (p5 ∨ (((p3 ∨ p5) → (p2 ∨ True)) ∧ (True ∧ p3)))) ∧ (((p3 ∨ (p2 ∨ p5)) → True) → ((p3 ∨ p1) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428962662391820204131016638931 : ((((((((((p1 ∨ p3) → (((p2 → p3) → False) ∧ (p1 ∨ p3))) → p1) ∧ p2) ∨ (p1 → p3)) ∧ p2) → (False ∧ p3)) ∨ (p4 → True)) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614842950253333334417146737076 : (((((p2 ∨ (p5 ∨ ((False ∨ (p1 → ((p2 ∧ ((p2 ∨ False) → p2)) ∨ True))) ∧ (p3 ∨ False)))) ∨ (p2 ∨ ((p2 ∧ p4) ∧ p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186379497991672438564571495225 : (((True ∧ ((p5 ∧ (p4 ∧ ((p2 ∨ p3) ∨ p4))) ∨ True)) → False) → (((p3 ∧ (p4 ∧ p2)) ∨ ((p4 ∨ p5) ∧ (p4 ∨ p2))) ∧ (p2 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((p5 ∧ (p4 ∧ ((p2 ∨ p3) ∨ p4))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ ((p5 ∧ (p4 ∧ ((p2 ∨ p3) ∨ p4))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ ((p5 ∧ (p4 ∧ ((p2 ∨ p3) ∨ p4))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227736127945765444149771731692 : ((p1 ∧ (False ∨ p4)) ∨ (((p5 ∨ p3) ∧ p5) → ((False ∨ ((p3 → p3) ∨ (p2 ∧ True))) ∧ (((True ∨ p5) ∧ p5) ∨ (p5 → (p3 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811424389626376868216687466955 : (((p5 → (p3 ∨ ((((((False → (True ∧ p2)) → p4) ∨ (p5 → ((False → ((p2 → (p3 → p4)) ∨ True)) ∨ True))) → p3) ∧ p5) ∨ p5))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178354203190503318245228785015 : (((p1 ∨ (p5 ∧ (((p3 ∨ (p4 ∧ p4)) ∧ p3) ∧ p5))) ∨ (p5 ∧ p1)) ∨ (True ∨ (((False ∧ ((p5 ∧ p3) ∧ p3)) ∧ (p5 ∨ p1)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180008800092118899318065756492 : ((((p2 ∨ p1) ∨ ((((True ∨ p5) ∨ (True ∧ p4)) → True) ∧ p2)) ∨ False) → ((True ∧ (p5 ∨ ((False → ((False → False) ∨ p5)) → p2))) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62923643456040339210821766120 : ((p4 ∧ (False ∧ (p3 → (p3 → (((p5 ∧ p1) ∨ (((p3 ∨ True) ∨ ((p4 ∧ True) ∧ p5)) ∧ ((p1 → (p3 ∧ p5)) → p5))) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317838047499156790720749831686 : (p4 ∨ (((True ∧ (p3 → p1)) ∨ (p3 ∧ (False ∧ (((False ∧ p2) ∧ (((p1 → p3) ∧ (True ∨ False)) ∨ p5)) ∧ (False ∨ (p3 → p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22335637706539446098155139122 : ((((((p3 → p1) → False) → p2) ∧ (p5 ∨ True)) → (p2 → (p2 ∨ (p3 ∨ (((p2 ∧ False) ∨ ((p4 ∨ (p2 ∨ p1)) ∨ p4)) ∧ p3))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
theorem thm_5_vars_192836407534069529086015995153 : ((((False ∨ ((True ∨ p3) → p3)) ∧ p4) ∧ (p5 ∧ True)) → (((((p5 → p2) → p5) → ((False ∧ p4) ∨ p3)) → (True ∨ p1)) → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149041847135652754372019000372 : (((p1 ∨ (p3 ∧ p3)) ∨ (p1 → ((((p5 → p2) ∨ True) → ((p5 ∨ True) ∧ False)) ∧ ((p1 → False) → p2)))) ∨ (False → (True ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259704993972735813663154195812 : ((p1 → p1) → (((p4 ∨ p1) ∧ p5) ∨ (p3 → (((False ∨ False) ∨ ((p1 → (p5 ∨ ((p4 → p3) ∨ True))) → (False ∨ p3))) ∨ (p2 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56994132211808099825371792063 : (((p5 ∨ (False → True)) ∧ (((False ∧ (((False ∧ False) → p5) ∧ ((p1 ∧ (True ∧ (p5 ∧ p3))) ∨ True))) ∧ p4) ∧ ((True ∧ p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198370561354779295167098947547 : ((p3 ∧ (((p4 ∧ p5) ∧ (True → p5)) ∨ False)) ∨ (((p5 ∧ (p3 ∨ p2)) → p5) ∨ (((p2 → (((p4 ∨ p2) ∧ p4) → False)) ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114314108381104177583576283661 : (((((p3 ∨ (p4 ∨ True)) → p4) ∨ ((p1 → (((p1 ∨ (False → p1)) → p5) ∧ p3)) ∨ p2)) ∧ (p2 ∨ ((p1 ∨ p4) → True))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120329355809988221095150741643 : (((p2 ∨ ((p1 ∨ (p5 ∨ ((p2 ∨ p3) ∨ (((p2 ∧ (p2 ∧ True)) ∧ ((True → p3) → (p5 → p3))) ∨ p5)))) ∧ p4)) ∧ p1) → (p5 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h17.left
            let h20 := h17.right
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174197391069210613589626398520 : ((((((p4 ∧ (p5 ∧ (p2 → p2))) ∨ (p2 → False)) ∧ p4) ∨ p4) → (p3 ∧ p2)) → ((p3 ∧ (((p4 ∧ False) ∨ (p2 ∨ False)) → p5)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323664157418102231077563207677 : (p5 ∨ (((((((False → p1) ∧ (p4 ∨ True)) ∧ p2) → (p2 → p5)) ∨ (p1 ∨ p1)) ∨ (p1 ∨ (p3 ∨ False))) ∨ (((p4 ∧ p1) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347377887863111340394258153989 : (p3 → ((((p5 ∨ (True ∧ True)) ∧ True) → (p2 ∨ False)) ∨ (p2 ∨ (True ∧ (p4 ∨ (((True ∨ (p4 ∨ ((p2 ∧ p3) ∧ p1))) ∧ p3) ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119072748198523279288982139055 : ((p1 → ((((p5 ∧ (p4 ∧ True)) ∨ (((p2 → ((p5 ∧ False) ∨ (p1 ∨ (p4 ∧ p1)))) ∨ p5) → p3)) → p5) → (p5 ∧ p4))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2687089876952107460722761488 : (((p2 ∨ ((p1 ∨ True) → p4)) ∨ p1) → ((True ∨ p3) → (p5 → (((p2 → p3) ∨ (p4 ∨ True)) ∨ (p2 ∧ (p4 ∧ (p2 ∨ True))))))) := by
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
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319166988288664319009442813150 : (p4 ∨ ((((p2 → ((False ∨ True) → (p5 ∨ (p1 → (p2 → p3))))) ∧ (p3 ∨ p2)) → (False ∨ p1)) ∨ ((True ∨ True) → ((True ∨ p3) → True)))) := by
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
theorem thm_5_vars_178357738075210511440738142538 : (((p5 ∨ (((True ∨ p2) → False) ∧ (p1 ∧ (p1 → p1)))) ∨ (p1 ∧ False)) ∨ ((True ∧ (True → (p3 → (((p4 ∧ p5) → True) → True)))) ∧ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106941808246904071333601428566 : (((p5 → (True ∨ (False → False))) ∧ (((False ∧ p3) ∧ (p1 ∧ p5)) ∨ (True → (p2 → (((p4 ∧ p2) ∧ (False ∧ p2)) → p2))))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166220731091776346517136360164 : ((p2 ∧ ((((p3 ∨ (False ∧ p2)) ∨ (p5 → (p1 ∨ (p4 ∨ False)))) ∨ p5) ∧ (p4 ∨ p1))) ∨ (((p1 → (p5 ∧ (p5 ∨ False))) ∧ p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686525510163106658832285306347 : (((((p5 ∨ (False ∧ p5)) → (p3 → ((((True → p2) ∧ p2) ∧ ((p5 → p3) ∨ p4)) ∧ p5))) → ((p5 ∧ (p5 ∧ p4)) ∨ (p3 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60036619945234349379266921505 : (((p1 ∨ p4) → (((p5 ∨ (p2 → p5)) → (False ∧ (True → (((p5 ∧ (p2 → p2)) ∧ (True ∨ ((True → p1) → True))) → p1)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603227148038542710026063601735 : ((((p2 ∨ ((False ∨ (p5 ∧ ((False ∨ (True → p5)) ∨ p4))) ∧ (((p3 → False) ∨ (p4 ∨ p3)) ∧ ((p3 → (False ∧ p4)) ∨ p5)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306646741932434736782707580735 : (p1 ∨ (True ∧ ((p3 → (((p3 ∧ (p1 ∧ (False ∨ (p2 ∨ True)))) → (p5 ∨ (p4 ∧ p1))) → (((p2 → True) → p2) → p2))) ∨ (p3 ∧ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14861372526278595164527032857 : ((((p5 → ((((True ∨ (p5 ∨ False)) ∧ True) → p5) → p4)) → (p4 → (False ∨ (((p1 ∨ (False ∨ p4)) ∧ p3) ∧ p1)))) ∨ (True ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116600045514592664239915952650 : (((p5 ∨ p3) ∧ (p2 → (((p3 ∨ (True ∨ (p1 ∧ False))) ∧ ((True ∧ (False → p4)) ∧ (p3 → False))) → (p2 → (p1 ∧ False))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182471966235921112657753316285 : (((p1 ∨ (p1 ∨ (p2 ∧ ((p3 → False) → False)))) ∨ (p1 ∨ True)) ∧ (p5 → (False → ((((p4 ∨ (p3 → p3)) ∧ (p5 ∧ p3)) → p4) ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- False on the left can always be used.
    apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43759613267260273434490172944 : ((((p2 ∧ ((((((True ∨ p5) → p2) ∨ ((p3 → p4) ∨ p2)) → p4) → True) → ((p1 ∧ (p4 ∧ p3)) → (p2 ∧ p5)))) → p2) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



