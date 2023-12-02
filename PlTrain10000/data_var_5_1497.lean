variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314536497272269215455679448773 : (p3 ∨ ((((p1 ∧ p2) ∧ ((((False ∧ p5) → p5) ∨ (p1 → (p1 → (False → p5)))) ∨ True)) ∨ False) ∨ (p4 ∨ ((p1 ∧ (p4 → p4)) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117860935533284227240350136379 : ((p5 ∧ ((False ∨ ((((p1 ∨ (((p5 ∨ (p5 ∧ True)) ∨ ((p3 ∧ p2) ∨ (True ∨ p1))) → p4)) → p1) ∧ p2) ∨ p1)) ∧ p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191879319210910602681412134113 : ((p4 ∨ (p2 ∧ (True ∧ (False ∨ ((p2 ∧ p1) ∧ True))))) ∨ ((p3 ∧ (((False → (p3 → p5)) → True) → ((p4 ∨ p5) ∧ p1))) → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False → (p3 → p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((False → (p3 → p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636497183583809554646762286276 : ((((((True → (True → ((p1 → p3) → (p3 ∧ ((p4 ∧ p2) ∨ p3))))) → False) ∧ (((True ∧ False) → ((p2 ∧ p2) ∨ p3)) → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112440957684495136617519751134 : ((((((((p4 ∨ ((p5 ∧ (p2 ∧ p2)) ∨ True)) ∨ ((p5 ∨ p3) ∨ (p2 → p3))) ∨ (p5 ∨ p4)) ∧ p3) → p1) ∨ p5) → p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669696629486812604942798613444 : (((((p3 ∨ (((p2 → False) → (p5 → ((p1 ∧ (p5 → p2)) → p5))) ∨ (p4 ∧ False))) → (False ∨ (p5 ∨ False))) ∨ ((p1 → True) ∨ p1)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144752406191144982053200749818 : (((((((p1 → False) ∧ (p2 → False)) ∧ True) ∧ ((p5 → p3) → (p2 ∨ p4))) ∨ False) ∨ ((False ∨ False) → p5)) ∧ (True ∨ ((False ∧ False) ∨ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262271039268065334761144012983 : (True ∧ ((((((((((p4 → True) ∨ p5) ∨ p2) ∨ (p5 → p1)) ∨ True) → (p5 → p1)) ∧ True) ∧ False) ∨ (False ∨ ((p1 → p3) ∧ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228432344759216697074826281732 : ((False ∨ (p5 ∧ p3)) ∨ ((((p3 → True) → ((p1 → False) ∨ p4)) ∨ ((False ∨ p4) ∧ ((p1 → p1) ∨ (False ∨ (p2 → p4))))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157476965805126573188155069067 : ((((((p2 ∨ (p4 ∧ p4)) ∧ ((p3 → (p4 → True)) ∨ p2)) ∨ p1) ∨ (p1 → False)) ∨ (p4 ∨ p1)) ∨ (False ∨ ((False → p4) ∨ (False → p3)))) := by
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
theorem thm_5_vars_237955155056289837623463532265 : ((True ∨ False) ∧ ((((True ∨ (p4 ∧ p5)) → (p1 ∨ p1)) ∧ (p3 → ((True → p3) → p1))) → (((p4 ∨ p1) ∨ ((p5 ∨ p4) ∨ p1)) ∨ p4))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p4 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313149929475157644645086335010 : (p3 ∨ (((p4 ∧ ((p1 ∧ p3) → (((True → (True → p4)) ∧ p4) ∨ (p1 ∧ p4)))) ∨ ((((p5 ∧ p4) ∧ (p2 ∨ p3)) ∨ True) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302557695331025907813572843199 : (False ∨ (p1 ∨ (((((((((p5 ∨ p3) ∨ (False ∧ p5)) ∨ (False → p4)) → False) ∨ True) ∧ (p5 ∧ p4)) → (p1 ∧ False)) ∨ (p4 → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209196297727965737219630333513 : ((p4 ∨ ((True → p3) ∧ (p2 ∨ p5))) → (((p1 ∨ p5) ∧ (p4 → p1)) ∨ (True ∨ (p5 ∧ (((p5 ∨ p2) ∧ ((p1 ∨ True) ∧ False)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49526270932547946600249170194 : (((((p1 ∧ (p5 → ((False → p5) ∧ (p4 → ((p4 → p1) → (p2 ∨ p4)))))) ∨ (p1 → p4)) ∨ (p1 ∨ False)) → ((True → False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478092692641733219845888895627 : (((((p4 ∨ p4) → (((p1 ∨ (False ∨ False)) ∧ False) ∧ p4)) → (True ∧ (p1 → ((p4 ∧ p2) ∨ ((True → False) ∨ ((p1 ∨ False) → True)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329341403489856576099609141314 : (True → (((p1 → p3) ∨ p4) → ((p4 → (((p5 → False) → (p2 ∧ ((False → (p5 → p1)) ∧ ((p4 ∨ p3) → (p4 ∧ False))))) ∨ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3221293507377300180447575066 : ((False ∨ p2) ∨ (p5 → (p3 ∨ (((((p1 ∧ p2) ∧ p2) ∧ p4) ∨ p1) ∨ (p4 → (False ∨ (False → (True → (p4 ∧ (p3 → False)))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61473842476022708852200158113 : ((p1 ∧ (((((p3 → (True ∧ (True → p4))) ∧ ((p5 ∧ (p4 ∨ p5)) ∨ (p2 → p4))) ∨ (p1 → p4)) ∨ (p5 ∧ p3)) → (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48978107141942985503907744432 : (((((p1 ∨ ((((p2 ∨ (p3 ∧ False)) ∧ p3) ∧ (p5 ∨ p5)) ∨ p1)) ∧ ((p4 → p2) ∨ (p4 ∨ True))) ∨ False) ∨ ((p2 → True) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157974440156615501899059843151 : (((p3 ∨ ((((p5 ∨ False) ∨ p4) ∧ p3) ∧ p3)) ∨ (((True → p4) → ((False ∧ p3) → p4)) ∨ p2)) ∨ (((False ∨ (p5 ∨ p5)) → p4) ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608350052820106224162029863725 : (((((((True ∨ p4) → ((p2 → ((((p3 → (p5 ∧ p3)) ∧ p2) ∨ p4) → False)) → ((p5 ∨ p2) ∧ (p3 → p3)))) ∨ p1) ∨ False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_785356442467016986012930308959 : (((p4 ∨ (((p4 ∨ ((p4 ∨ (((p5 → p5) → (p3 → (p5 ∨ p5))) ∧ ((p1 → p5) → p2))) ∧ (True → (False ∧ p2)))) ∨ p1) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_951493433783367217331003332757 : ((((True → (p4 ∧ p1)) ∧ (p1 ∨ ((p2 ∨ ((p4 ∧ p1) → (((p1 ∧ ((False ∧ (p1 ∨ p3)) ∧ p3)) ∨ False) → (p3 ∧ p4)))) ∧ p1))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618666054868100876002553556985 : ((((((p2 → p3) ∧ True) ∧ (p2 ∧ (p2 ∧ (((p1 ∧ (((False ∧ False) ∨ ((p1 → False) → p4)) ∧ p1)) ∨ (False → p3)) ∨ p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708516329060049972438860935898 : ((((((((p1 ∨ p2) ∨ p1) → p3) → True) ∨ False) → (p3 ∨ (((p1 ∧ p2) ∨ ((p3 ∨ (p4 ∧ True)) ∨ p3)) ∧ ((True → p1) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256883533641635801191669356137 : ((p1 ∨ p4) → (((p2 ∧ p4) → ((((p2 → (((p3 ∧ False) ∧ p3) ∨ p1)) ∨ ((p3 ∨ p2) ∧ True)) ∨ (p1 → p1)) ∨ (p5 → p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79084027082261898068939982476 : (((True → ((((p3 → (True → False)) → (((p3 → (p2 → True)) ∨ (True → (p5 → (False → p5)))) ∨ True)) ∧ False) ∧ p2)) ∧ (p5 ∨ p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41465570469747324468681332453 : ((((True → ((p1 → (p1 ∨ p1)) → (p5 → (False ∨ (p5 → p1))))) ∧ (p2 → (p5 → ((p5 ∧ (p5 ∨ p1)) ∨ (False ∧ True))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152311563846977952083750950395 : ((((p4 → (False ∧ p2)) ∨ p3) ∧ ((False ∨ ((((p3 ∨ ((p1 ∧ p4) → p4)) ∧ p1) ∨ p1) ∨ p5)) ∧ p2)) → ((p3 ∨ False) ∨ (p4 → p3))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h16 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h15
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h17 := h4 h16
            -- We need to get the left conjuct of h17 based on <expert-advice>.
            let h18 := h17.left
            -- False on the left can always be used.
            apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h21 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h21
          -- We need to get the left conjuct of h22 based on <expert-advice>.
          let h23 := h22.left
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h26 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h27 := h4 h26
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h38
          case inr h39 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29
        case inr h40 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160982739816240201492810108546 : (((p4 → (p3 ∧ p5)) ∧ (((p1 ∨ p5) ∧ p5) ∧ (((p3 ∨ (p4 ∧ (p5 ∧ p2))) ∨ p3) ∨ p3))) → (p5 ∨ (p2 → (p3 ∧ (True → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148866425575894782093085514046 : (((p2 → ((p2 ∨ p5) ∨ p4)) ∧ (((False → (p5 ∨ p4)) → ((p1 ∧ p3) ∨ p4)) ∧ ((p4 ∧ p3) ∧ p3))) ∨ ((False ∧ True) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612522692315608216146448108798 : (((((((False → (p4 ∧ True)) ∧ (False ∧ ((p3 ∨ False) ∨ (((p3 → (p5 → (p2 → p2))) ∧ False) ∧ True)))) ∨ p2) ∨ (True → p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187660427054228158301127634547 : ((True → (((p5 → (True → (p5 ∨ (p2 ∧ p2)))) ∨ p1) → False)) → (p1 → (((p3 ∧ ((True ∧ (p3 ∨ p4)) ∧ p4)) ∧ p4) ∨ (p1 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204320959569719417268954384015 : (((p2 ∧ (p1 ∨ (p3 ∧ p5))) ∧ True) ∨ ((((True ∧ p2) ∨ (p2 ∨ (((False ∨ p2) ∧ p1) ∧ p5))) → (p5 ∧ (p2 → False))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35107274621724956632647271200 : ((p1 → ((((p5 ∧ (True → (True ∧ (p1 ∨ ((p1 ∧ p1) ∨ (p4 ∨ p5)))))) → False) ∧ p4) ∨ (p1 ∨ (((p3 → p5) → p1) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231113047825302012268893150109 : (((p1 ∨ True) ∨ p1) → (((p5 ∧ p2) ∨ ((((((True ∧ True) → False) ∧ True) ∧ p2) ∧ p1) → (p4 ∨ False))) ∨ ((p5 ∧ (True ∨ p2)) → p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : (True ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117913749577879838212268341782 : ((p5 ∧ (((p1 ∨ False) ∧ (p3 ∨ ((p2 → True) ∨ p2))) ∨ (((p4 ∨ p4) ∧ False) ∨ (((False ∨ p1) → (False ∨ p5)) ∨ p5)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209174388614019603197500160510 : ((p3 ∨ (p4 → (p5 ∨ (p2 ∨ p4)))) → (((False ∧ p1) ∨ p3) ∨ (False → ((False ∨ False) → ((((p4 → p2) ∨ p2) → (p2 ∨ True)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64020696403429823574961031536 : ((False ∨ ((p4 → ((p4 → ((((True ∧ p5) → p5) ∧ (p1 ∨ ((False ∧ p5) ∧ (p1 ∨ True)))) ∨ (p4 → False))) ∧ p2)) ∨ (True ∨ False))) ∨ p3) := by
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
theorem thm_5_vars_225731636644272229098829302990 : (((p4 → p1) ∧ p1) ∨ ((((True ∨ (((p2 → (p5 ∧ False)) ∨ (p1 ∧ p1)) ∨ (p1 → p5))) → (True → p2)) ∨ (p1 ∨ False)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151087253910710978751501558743 : ((((p2 → (((p2 ∨ (((p2 ∧ p5) ∨ p1) → (((False ∧ p4) ∨ False) → p5))) → p4) ∧ p5)) ∨ True) → False) → ((True → (True ∧ p1)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → (((p2 ∨ (((p2 ∧ p5) ∨ p1) → (((False ∧ p4) ∨ False) → p5))) → p4) ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → (((p2 ∨ (((p2 ∧ p5) ∨ p1) → (((False ∧ p4) ∨ False) → p5))) → p4) ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327153821107615784828491470133 : (True → ((p3 ∧ (p3 ∨ (((((p2 ∨ p5) → False) → p4) ∨ ((False ∧ (p5 → True)) → False)) → (False ∧ (p1 ∧ ((p4 ∨ True) ∧ True)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186767952911199062934786331799 : (((p4 ∧ (((p3 ∧ False) → True) → True)) → ((p3 ∨ p3) → p1)) → (p1 → (((p5 → (p3 ∧ (p2 → (p2 ∨ (False ∨ p2))))) → p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254160550029311109664062048329 : ((p2 ∧ p1) → ((((p3 ∧ p5) ∨ p3) ∨ (((p4 ∨ p3) → p1) ∧ (((p1 → (((p5 ∨ p5) ∧ False) ∧ p3)) → p2) → p5))) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347481709948067116110189979148 : (p3 → (((p4 → (p1 ∨ p1)) ∧ (True → p3)) ∨ ((p1 ∧ p1) ∨ (False ∨ ((p5 ∧ p4) ∨ (False → ((((p4 ∧ False) → p1) ∨ p1) ∨ p5))))))) := by
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
theorem thm_5_vars_178628075487897602698562241882 : ((((True ∨ (False → True)) ∧ (False → p1)) → ((p5 ∨ p4) → (p4 ∨ p4))) ∨ (((p2 ∧ p1) → ((p1 ∨ (p3 → p2)) ∧ p1)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135191552711852093679471087913 : (((((p2 ∨ ((True → (p3 ∨ p4)) ∨ p4)) ∧ ((True → (False → (p3 ∧ (False ∧ p2)))) ∨ p4)) → p1) → (False ∧ p2)) ∨ (False → (p4 ∧ p3))) := by
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
theorem thm_5_vars_615525165011088968226116311702 : ((((((((p2 ∨ ((p4 ∨ p5) ∧ False)) → p4) → p1) ∨ ((p2 ∨ p1) ∧ (True ∨ p5))) → (p4 ∨ (((p3 ∧ p2) ∨ p4) ∨ p1))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765072276457616778394603476344 : (((p4 ∧ (((p5 ∧ (p5 ∧ (p2 ∧ p5))) ∧ ((False → (True ∧ (((((p3 → p3) ∧ p2) ∧ p5) → p1) ∧ p2))) ∧ p4)) ∧ (True ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118117825237842011389372089491 : ((False ∨ (((p4 ∨ p1) → (((((p1 → False) ∨ ((p2 ∨ False) ∧ False)) ∨ (p3 ∧ (False ∨ (p1 → p5)))) → p1) ∨ p4)) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319046570525917776486353100279 : (p4 ∨ ((((p4 ∨ (p2 ∨ (False ∨ (p2 ∧ p2)))) ∨ True) → ((True ∨ (p5 → (True ∧ True))) ∧ (False ∧ p2))) ∨ (True ∨ ((p2 → True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55206710357646703835925060276 : (((((p5 → p1) → p4) ∧ (p5 ∨ True)) ∨ ((p2 → p5) ∨ ((False ∧ p5) ∨ (p1 ∨ (((p3 ∨ p4) ∧ ((False → p3) ∧ True)) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134417386396423554335531192824 : (((p3 → (((((p4 ∧ p2) ∧ p2) → True) ∧ (p2 ∨ (((((p1 ∨ True) → True) ∧ False) ∧ p4) ∧ p2))) ∧ p4)) ∨ p5) ∨ ((False ∧ p4) → p5)) := by
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
theorem thm_5_vars_171354105636982158230222216619 : ((((p2 → ((((p5 ∧ (p2 ∨ p2)) ∧ (p4 ∧ p2)) → p4) ∨ p3)) → p5) ∧ True) ∨ (((False ∧ (True → p5)) ∧ True) → (p3 ∧ (p2 ∧ p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336199396401413222721376517306 : (p1 → (((((p3 → (p3 ∨ (p1 → ((p5 ∧ p1) → (False ∧ (p3 → True)))))) ∨ False) → ((True → (p3 ∨ p4)) ∧ p3)) ∨ (p1 ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713893035205784267930255598761 : ((((((p5 → p1) → (p3 ∨ False)) ∨ p2) → (((p4 ∧ (False ∨ p1)) ∨ (p3 → (False → (True ∨ ((p2 ∨ p2) ∨ False))))) → (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343399856393237849167207323401 : (p2 → ((p3 ∧ p1) ∨ (p3 → (((((p1 ∨ False) → (p4 → (p1 → p4))) → p1) ∨ ((p5 ∧ ((p2 ∧ p2) ∧ p4)) ∨ (True ∧ True))) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113694630816875193664069272446 : (((((((p5 ∧ p1) ∨ False) ∨ p5) → (p3 ∧ ((True ∨ p3) ∨ ((p5 ∧ p2) ∧ (p3 ∧ (p3 ∨ False)))))) → p4) → (p3 ∨ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738477187993002464657231142373 : ((((p1 ∧ p3) ∨ ((((p3 → (p2 ∨ True)) → (True ∨ (p4 ∧ (p2 ∧ (p1 → p4))))) → p2) ∨ (p5 ∨ (((p3 ∧ p5) → p3) ∧ True)))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251002824826376376408192588540 : ((p1 → p5) ∨ ((p1 ∧ ((((p1 → (((p4 → (False ∧ p4)) ∧ (False ∨ p5)) ∧ p4)) → False) → ((False ∧ True) ∧ p4)) → p3)) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304976758124901994000847639399 : (p1 ∨ ((((((p5 → p4) ∨ (p3 ∨ (((p4 → ((p5 ∧ True) ∨ p1)) ∨ p3) → True))) → False) ∨ (True → p5)) ∧ True) ∨ (p2 → (p5 ∨ p2)))) := by
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
theorem thm_5_vars_308400448947142820366925069712 : (p2 ∨ (((p2 ∨ (((p1 → p4) ∨ ((p4 ∧ True) → p4)) → (((((p1 → p4) ∧ (False → p3)) → p5) → p4) ∧ (p4 → False)))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153308362341410206519418934271 : ((p1 ∨ (((p4 → (True ∧ (p5 → p2))) → p3) ∨ (p4 ∨ ((True ∧ (p5 → p5)) ∨ (p1 → (p3 → p3)))))) → (p3 ∨ (p5 → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354911057071760416259896318622 : (p5 → ((False ∨ ((((p2 → p2) ∧ p2) ∨ (p1 → ((p3 ∧ ((p2 ∨ ((False ∧ p4) → ((p4 ∨ p2) ∨ p1))) ∧ False)) ∧ p1))) → p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42756087046559446656580676388 : (((True → (p3 ∨ (((((p4 ∨ p5) ∨ (True ∨ p3)) ∧ False) ∨ (p5 ∧ ((p1 ∨ (p2 ∨ ((p4 ∨ p2) → p4))) ∨ p5))) ∨ True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51985972673866066237485164722 : ((((p4 ∨ p3) ∨ ((False → p5) → (((p5 ∧ ((p1 → False) ∨ False)) ∧ True) ∨ p5))) ∨ ((p5 ∧ (False → (p3 ∧ p1))) ∨ (False → p4))) ∨ p3) := by
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
theorem thm_5_vars_47617870796511145503846618397 : (((p5 → (((((True → (False → (((p1 ∧ p3) ∧ p2) → False))) ∨ p1) ∧ True) ∧ (((p4 ∨ p4) ∨ p1) → True)) → p2)) ∨ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173047394799513493090542935638 : ((False ∨ ((p3 → (((p5 ∨ (p5 ∧ (False → False))) ∨ p1) → (p1 ∧ p5))) ∧ False)) ∨ (p1 → (((True ∨ p1) → p1) ∨ (p1 ∨ (p5 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197769221248396723227740506961 : (((p4 ∨ (p2 ∧ p5)) ∧ ((False ∨ p4) ∨ p3)) ∨ ((((p1 → (False ∨ False)) → (p5 ∧ p4)) ∨ (p5 → p5)) → (((p1 ∧ p2) ∧ p3) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342293509933326416704371230447 : (p2 → (((p1 ∧ p4) ∨ (((p5 ∨ (p1 → ((True ∨ p3) ∨ p3))) ∧ p1) ∨ ((p5 ∨ p5) ∨ p4))) ∨ ((p4 ∧ (p4 ∧ p1)) → (p2 ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260605650417965603478344953789 : ((p3 → p2) → ((True → (True → (p2 → (p1 ∨ ((False ∨ ((p4 ∨ p5) ∧ (p1 → False))) → p1))))) ∨ (True → (((True → False) ∨ False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116775119360195466485982072066 : (((False ∨ p3) ∨ (((((p5 ∧ p3) ∨ p2) ∧ p3) ∨ (((False ∨ p2) ∨ ((p5 ∧ (False → (p4 ∧ True))) → True)) ∨ False)) ∨ p1)) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337370453116972412632666674590 : (p1 → ((((p5 ∨ ((p2 ∨ (True ∨ False)) ∨ p1)) ∨ p3) → (((p4 ∨ (True → p2)) → False) ∨ (True → (p3 → p1)))) ∨ (p1 → (p1 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655344245248675448331518150918 : (((((((True ∧ p5) ∨ (((False → ((p2 ∧ False) ∧ p3)) → (p3 ∧ p4)) → ((p4 → False) ∨ p4))) ∧ p2) ∨ (p4 ∨ False)) ∨ (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141733814939544699936597197334 : (((p5 ∨ p4) ∧ (((True → ((False ∨ (p5 → p1)) ∧ p4)) ∨ ((p1 ∨ p4) ∧ p3)) ∧ (((p4 → p2) ∨ p4) ∧ p1))) → ((True → False) → p4)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h7.left
        let h20 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h23 := h2 h22
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h7.left
        let h27 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h4.left
    let h32 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h37 =>
        -- One of the premise coincides with the conclusion.
        exact h37
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h32.left
        let h43 := h32.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h44 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h45 =>
          -- One of the premise coincides with the conclusion.
          exact h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h32.left
        let h48 := h32.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h49 =>
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h50 =>
          -- One of the premise coincides with the conclusion.
          exact h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662637574127199649591645295956 : ((((((p5 ∨ p3) ∨ (p5 → p2)) ∧ ((p2 ∧ p1) ∧ ((((((p3 ∧ p5) → p1) ∨ (False → True)) ∧ p5) ∧ p4) → p4))) → (p5 → p2)) ∨ False) ∧ True) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h4.left
      let h13 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148123929679221228112979920550 : ((((False → (p4 ∨ False)) ∧ (p5 ∨ ((p2 ∨ (p3 ∧ ((False → (p3 ∧ True)) → True))) → p1))) → (p2 → p4)) ∨ (((p4 ∧ p5) ∧ p2) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246581581175544726016971338035 : ((p5 ∧ p2) ∨ ((p4 → (p2 → (p5 → (((p4 → p3) → p4) → True)))) → (p5 ∨ (((True ∧ (p5 ∧ p2)) ∨ ((p2 → p5) ∨ p3)) ∨ True)))) := by
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
theorem thm_5_vars_53439178344846217964016805535 : (((((p2 ∨ False) → p5) ∧ (p5 → (((False → p2) → p1) ∧ p4))) → ((((p2 ∧ (((p4 ∨ False) ∨ p1) ∧ p3)) ∨ False) → p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207577617317507345314496120356 : ((((p1 ∨ (True ∧ p3)) ∨ p1) → p3) → (p1 → (p4 ∨ (p5 → (((p4 ∨ (True → p1)) ∧ ((p5 ∨ p3) ∧ True)) → ((p4 ∧ p2) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ (True ∧ p3)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h8.left
    let h16 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209068111815134642344120074817 : ((p1 ∨ (p4 ∧ ((False ∨ False) → p4))) → (((p3 ∧ (p5 → p4)) ∧ p1) ∨ (((((True → True) → (True ∨ p4)) ∧ p4) ∨ (p1 ∨ p1)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234767247382460936875513095468 : ((p4 → (p5 → False)) → (((p2 ∨ ((True → p5) ∧ (p2 ∨ ((p3 → False) ∨ ((p4 ∨ (p1 ∨ True)) ∨ True))))) ∨ p1) → ((p3 ∧ False) ∨ True))) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
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
              -- Disjunctions on the left can always be decomposed.
              cases h14
              case inl h15 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h16 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177689587785827921201970440610 : (((((p1 ∧ (((p3 → p2) → False) → True)) → False) ∧ (p3 ∧ p2)) ∧ p3) ∨ (((p2 ∨ p1) ∧ (p3 ∧ ((p2 ∧ True) → (p3 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49427830708588951901508699613 : ((((((p1 ∨ (((False ∧ ((True ∨ False) ∨ p2)) ∧ p2) ∨ (p5 → (p3 → p3)))) ∧ (p2 → True)) ∨ False) ∨ p3) → ((False → p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654765139357485803232779123882 : ((((((((False ∨ ((False → p3) ∧ ((True ∨ p1) ∨ (p5 → p1)))) ∨ p5) ∧ ((True ∨ (p2 ∨ p2)) → p2)) → p1) → False) ∨ (p2 ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_59787870141820298134305802356 : (((p2 ∧ p1) → (True → ((True ∧ p3) ∨ ((p4 → False) → (((p3 → p3) ∧ (p2 → p1)) → (((p5 → False) ∨ p3) ∧ (p3 ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797095513794853610613679444888 : (((p1 → (((p1 ∧ ((p2 → p1) ∧ False)) ∨ ((p4 → (True ∨ ((((((p1 ∧ p4) → True) ∧ p2) ∧ False) → True) ∧ p2))) → p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66372390941788970165726467162 : ((p5 ∨ (p2 ∨ ((((((False ∧ p2) ∧ True) ∨ p5) ∨ (True ∧ False)) ∧ False) ∧ (((p4 ∨ False) ∨ (p5 ∨ True)) → ((False ∧ p1) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147756139275730759482385193976 : ((((p5 → (p2 ∨ p2)) ∨ (((p5 → ((p2 ∧ (True → (p4 → (True ∨ p1)))) ∨ True)) → p2) → True)) → p5) ∨ ((False ∨ (p3 ∧ True)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77098503329738813938155544374 : (((((p5 ∧ False) ∨ (p3 ∧ p3)) ∨ (p3 ∨ ((p2 → (((p3 ∧ ((True ∧ p1) ∨ p3)) ∧ ((False ∧ p5) → True)) ∨ p2)) ∨ p2))) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ False) ∨ (p3 ∧ p3)) ∨ (p3 ∨ ((p2 → (((p3 ∧ ((True ∧ p1) ∨ p3)) ∧ ((False ∧ p5) → True)) ∨ p2)) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48448880127375032509725519047 : (((p5 → (((p5 ∨ p2) → p3) → ((p3 ∧ (p5 ∧ ((p2 → ((True ∧ p4) → p1)) ∧ p5))) ∨ (False ∨ (p5 ∧ p3))))) → (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142087138997934987963441588227 : ((True ∧ ((p4 ∨ True) → ((p1 ∨ (((p3 ∨ p1) → True) ∨ ((p1 → ((p3 → True) ∧ (True ∧ p1))) ∨ False))) ∧ p1))) → (p3 ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696817022101935811790607300708 : (((((p2 ∨ (((True ∨ p1) ∨ p2) ∧ ((p4 ∨ True) ∧ p4))) → p1) ∧ (p5 → ((p5 → (p2 → p4)) → (((p3 → p1) → p5) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58895998002192212105028465334 : (((False ∧ p4) ∨ ((((False ∨ ((True ∧ p3) ∧ ((p2 → p1) ∧ (p2 ∧ (False → False))))) → (p5 ∧ (False ∨ p5))) ∧ p2) ∨ (p4 ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_51939410194822946182218336482 : (((((p5 ∨ p2) ∨ ((p1 ∨ p2) ∨ (p4 → p5))) ∨ (p3 → ((False → p1) ∧ p3))) ∨ (p1 ∨ (((True → p4) ∨ (p3 ∧ False)) → True))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64725819319551219254082006342 : ((p1 ∨ (p5 → (((p4 → p5) → (((p5 → (p2 ∨ (((p2 ∧ False) ∧ (p5 ∨ (p2 → (p2 → p4)))) ∨ p3))) ∨ p2) ∧ False)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243422111183513702850599653312 : ((p5 → True) ∧ (((p1 ∨ ((p1 ∧ (p2 → p1)) ∨ p3)) ∧ ((True → False) ∨ p4)) → (p1 ∨ (((p1 ∨ p4) ∨ (True → (p3 ∨ p4))) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h15 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710843943282342221872706541481 : (((((p3 ∨ False) ∧ ((p3 ∧ p5) → p5)) ∧ ((((p2 ∨ (p4 ∧ p3)) ∧ p2) ∨ p5) ∨ (p5 → ((p3 → (p3 → (p5 → p3))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135445480818765752020861613740 : (((((p5 → True) ∨ (((p5 ∨ p5) ∧ (p1 ∧ ((p2 ∨ False) → (True → p2)))) ∧ p1)) ∧ True) → (p1 ∧ (p5 ∧ p3))) ∨ ((p1 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



