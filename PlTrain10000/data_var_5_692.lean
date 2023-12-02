variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150197559609616430428579591200 : ((p2 → (((p2 ∨ True) ∨ ((p4 ∧ ((p3 ∧ p3) ∧ True)) ∨ ((p5 ∧ p1) → ((p3 ∨ p5) → p2)))) → p1)) ∨ (True → (p1 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_694348640516632727529990695042 : (((((False → (True ∨ p5)) → (((p5 → (p2 ∨ p5)) → p2) ∨ (False ∧ p4))) ∨ ((False → (False → (p2 ∨ p5))) ∨ (True ∧ (p5 → False)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39765905084379928899446233022 : (((True → ((p4 ∧ ((False ∨ ((p2 → (p5 ∨ p2)) ∧ p1)) → False)) ∨ (((((p4 → p1) ∧ True) ∧ p4) ∧ p3) → (p4 → p2)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950045519586645401989267629662 : (((((True ∨ p2) → False) ∧ (p4 → (p5 ∨ (p2 ∧ ((((p1 ∨ (p1 → p1)) → (p4 → False)) ∧ (((p1 ∧ p5) ∨ p2) → p1)) → True))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217532026174699822024589595863 : ((((p3 → False) ∧ p2) → True) → ((p1 ∨ (p4 → p1)) → (((p4 ∧ p3) ∧ (p5 → (p2 ∨ p5))) → ((p5 ∧ p5) ∨ ((p1 ∧ True) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112276729919926921295985996913 : (((True → (((p2 → (True ∧ ((p4 → p4) ∨ False))) → (p3 ∧ ((p5 ∧ p1) ∨ p5))) → ((p2 ∧ p1) ∧ (p5 ∧ True)))) ∨ True) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112012885906415105619658501528 : ((((p1 ∨ (p4 ∨ (True ∨ p2))) → (((p4 ∧ ((p3 ∨ p2) ∨ (p5 ∧ True))) ∨ (False → (p5 → True))) → (p1 → p5))) ∨ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309901162608775334115069176094 : (p2 ∨ ((False ∨ (((True ∨ (p1 ∨ p4)) ∧ (True ∧ p5)) ∨ ((p5 ∧ False) ∨ (True ∨ (p5 ∧ True))))) ∧ (((p4 ∨ p4) → p5) ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614824057987342031315559920540 : (((((p3 ∧ (((p5 ∧ False) → True) → (p1 → ((p2 → True) ∧ (p4 ∨ (False ∨ (True → p5))))))) ∨ (True ∨ ((True → p5) ∧ p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131399390265238411887840480711 : (((((p2 ∨ p4) → p1) ∧ p2) ∨ (True → (((p4 ∧ False) ∧ (((p3 ∨ p5) ∨ (p1 ∧ p4)) → (p5 ∨ False))) ∨ True))) ∧ (p2 ∨ (p2 → p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172631708007800571852183942794 : (((p4 ∧ p1) ∧ (False → (((p3 ∧ p5) ∧ p1) ∨ (((p2 ∨ p5) ∨ p2) → True)))) ∨ (p5 → (((p4 ∨ False) → ((p2 ∨ p3) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137102345226376080177832611914 : ((True ∧ ((((False ∧ (p3 ∨ p2)) → p1) → (p4 ∨ ((p1 → (p2 → ((p2 → p5) → p5))) → p4))) ∨ (False ∧ p3))) ∨ (p3 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68307536274242658670972054493 : ((p3 → (((((False ∧ (True ∧ (True ∨ p4))) → (False → (p2 ∨ (p4 ∧ p5)))) → p2) ∧ (p5 ∧ p5)) ∨ ((p4 ∧ (p3 → p2)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66351244035904937989566813140 : ((p5 ∨ (p5 ∧ (True ∧ (((False ∨ p1) ∧ p4) ∧ ((p5 ∧ (False → p1)) ∧ ((True ∨ p4) → ((p1 ∨ (p1 ∧ (p2 ∧ p2))) ∧ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747678583570609867784184181486 : ((((False → True) → (((p3 → (True → ((p2 → ((False ∧ (True ∧ p1)) → ((p2 ∨ (False ∧ p4)) ∧ p5))) ∧ (False → p4)))) → p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171754713037693375084093320669 : (((((((p2 ∨ p4) ∨ (p4 ∧ ((p3 ∨ True) ∨ False))) ∨ p3) ∧ p1) → p4) → p1) ∨ ((p2 ∧ p5) → ((p4 ∨ ((False ∧ True) → p3)) → p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70881736808737739094721989269 : (((((True ∧ (((p4 → p3) ∨ True) → (p3 ∨ p2))) ∨ (p4 → p4)) → ((True ∧ p3) ∧ (p5 ∧ (p3 ∧ (p3 ∧ (False ∧ p4)))))) ∧ p5) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ (((p4 → p3) ∨ True) → (p3 ∨ p2))) ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354864011895627711525184961468 : (p5 → (((p4 → p3) → (p3 ∧ (((False ∨ p4) → ((False ∨ (True → ((((True → False) ∨ p5) ∨ p1) ∨ (True → False)))) → p2)) → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201093050110515016865090132394 : ((True → (((True ∧ (p2 → p4)) ∧ False) ∧ p4)) → (p3 ∨ ((((p4 ∧ p2) ∧ (False ∨ (p1 → (p4 ∨ (False ∧ p3))))) ∨ True) → (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221805606287071036092573034153 : (((p2 ∧ p3) → True) ∧ (p2 → ((((p3 ∧ False) ∧ p3) ∧ (p5 → False)) ∨ (((p2 ∧ True) → ((p3 ∧ (p4 → p1)) ∨ (False → p1))) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305865736207764343410957279100 : (p1 ∨ ((((p5 → False) ∧ (p1 ∧ p3)) ∨ False) ∨ (p4 → ((True ∧ (p4 ∨ (p2 ∨ False))) → ((p2 ∨ True) ∨ (((p2 ∨ p2) ∧ p1) → p5)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52678546001734339336952686423 : (((p2 ∨ (False ∧ (p2 ∧ ((True ∨ p4) ∧ (p1 ∧ ((p4 → False) → p4)))))) ∨ ((((p2 ∨ False) ∧ p4) ∧ ((p4 → p5) → p1)) → p4)) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225496139738920784092518825939 : (((p5 ∨ p1) ∧ p2) ∨ (((p2 ∨ p5) ∧ ((p2 ∨ (False ∨ False)) ∧ ((p4 ∧ (p5 ∧ False)) ∨ (True → (p1 ∨ ((p2 → False) ∨ p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149166206271422920057190572249 : (((p4 ∨ p1) ∧ ((p5 ∨ False) ∨ (p2 → (p3 ∧ ((p3 ∨ ((p2 → True) ∧ (p5 ∧ (p4 ∧ p3)))) → p5))))) ∨ (p2 ∨ ((p5 ∧ False) → p4))) := by
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
theorem thm_5_vars_173096901180807238518509097673 : ((p1 ∨ (p2 ∧ ((((True ∧ p1) ∨ ((p4 ∨ (p5 ∨ p5)) ∨ True)) → p1) → p1))) ∨ (True ∨ (True ∨ (((True ∨ p1) → (p2 → p1)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47096842844311859248414180438 : ((((((False ∧ (((p4 ∧ (p2 ∧ p4)) ∧ ((p4 ∨ (p4 → False)) ∧ p5)) ∨ p2)) ∨ True) ∧ p3) ∧ ((p3 → p2) → p2)) ∨ (True ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55160895481575146553868441554 : ((((p5 ∧ (True ∨ (p1 ∨ True))) ∨ p5) ∨ (p1 ∨ (p5 → (((True ∨ (p4 ∧ p3)) ∧ p3) ∨ ((p2 ∨ (p2 → (False ∧ p1))) ∨ True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_694029896474106546791143042609 : (((((p4 ∨ ((p3 → (p4 → (p4 ∧ (p3 ∨ p2)))) → p5)) → (p1 ∧ p4)) ∨ ((((p5 ∧ (p5 ∨ True)) ∨ True) ∧ (p1 → p3)) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_113382889998433624217615433886 : (((p5 ∨ (((True ∧ ((p3 ∨ (((p2 → (p2 ∧ p1)) ∨ False) ∨ p3)) ∧ p2)) → (p2 ∧ (False ∧ True))) → False)) ∧ (False ∧ p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619792908286424738204638583809 : (((((p1 ∨ p5) ∧ (((False ∨ p2) → ((True → ((True ∨ (p2 → p5)) ∨ ((True → False) ∨ p4))) → ((True ∧ False) ∧ p4))) ∧ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215058688632744408822412444125 : (((p4 ∨ p3) → (p4 ∨ False)) ∨ (((p5 ∧ False) ∨ (p2 ∨ p4)) ∨ (((p4 → (p4 ∨ p2)) ∧ p4) ∨ ((p1 ∧ True) → (True ∨ (p5 → p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609506170883213370209401636615 : (((((p1 ∧ (p2 ∨ ((p2 ∧ (p4 ∧ (p1 → p1))) ∨ (((p4 ∧ p2) ∧ False) ∨ (((p1 ∨ True) ∨ (p3 → p2)) → p1))))) ∨ True) ∨ p1) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_328111502736420537459323354428 : (True → (((((p3 → p4) → p1) ∧ (p2 ∨ ((p2 → p2) ∧ ((p3 ∧ p3) ∧ (False → (True ∨ p4)))))) ∨ (True ∧ p3)) ∨ (p1 → (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941130724331305771289057808707 : (((((p4 ∨ p5) ∨ (p2 ∨ (p5 ∨ True))) → ((True ∧ False) ∧ (p4 ∧ (p1 ∧ (((p4 ∧ (p5 ∨ (p1 ∧ p2))) ∧ (False ∧ p5)) → p4))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p5) ∨ (p2 ∨ (p5 ∨ True))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214153395940191540922627275627 : ((((False ∧ p2) → p4) → p3) ∨ (((((False → (False → p4)) → p3) → (p5 ∨ p1)) → (p1 ∨ ((p3 ∨ (p5 → p5)) ∨ p2))) ∨ (False ∧ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701646141083318962723920927248 : (((((p4 → p1) ∨ ((p5 ∨ p2) → ((p4 ∨ p5) ∧ p3))) ∧ (False ∨ ((True → ((p2 ∨ p4) ∨ ((p2 → (p4 ∧ p5)) → p3))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158163198983936817586997970566 : ((((True → (p3 ∧ True)) ∧ p5) → (False ∨ (p4 ∨ (p1 → (((p3 → p2) ∨ p3) ∨ (p1 ∨ True)))))) ∨ ((((p5 ∧ p4) → p3) ∧ False) → p5)) := by
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
theorem thm_5_vars_462921255700201915240345411732 : ((((((p5 ∨ (((p3 ∨ (False → True)) → p4) ∧ p5)) ∨ p4) ∨ ((False ∨ p3) ∨ p2)) ∨ (((p1 ∧ True) ∨ ((p3 ∧ False) ∨ True)) ∨ p3)) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314866713186404080154518579098 : (p3 ∨ (((False → ((False ∧ True) ∧ p4)) → ((p2 ∨ (p1 → False)) ∧ False)) → ((p3 ∧ ((p3 ∨ (p4 ∧ (False ∧ (p3 ∨ p5)))) → p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((False ∧ True) ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311238970350018985876947454727 : (p2 ∨ ((p4 → True) → ((True → ((True ∨ p3) → ((p4 ∧ (False → p2)) ∧ (p5 ∨ p5)))) → (((p4 ∨ p3) → ((p1 ∧ p4) ∨ False)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41702495161090561472424481018 : (((((p5 → (False → p4)) → (p2 → p1)) → (p4 ∧ ((p2 ∧ (p5 → (p3 ∨ (p3 ∨ (p5 ∨ (True ∧ p4)))))) ∨ (p3 ∧ p5)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217272899783539805819610797678 : (((p2 ∧ (p3 ∨ p3)) ∨ p5) → (((p3 ∨ (((True ∨ (p2 ∧ p1)) → (p1 ∨ p4)) ∧ (p1 ∧ False))) ∨ True) ∧ ((True → (True ∨ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207573397876692255438268072398 : ((((p3 ∧ (p5 → False)) ∨ p5) → p4) → ((p2 → p3) → (((p4 ∨ p2) ∨ (True ∨ p5)) → (((p1 → False) → (p5 → p4)) ∨ (p3 ∧ p3))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 ∧ (p5 → False)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h20 : ((p3 ∧ (p5 → False)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h21 := h1 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152094508101091908007510769883 : ((((p2 → (p2 → p1)) ∨ (((p4 ∧ p3) ∧ False) → p2)) → ((((p2 → p4) ∧ (p1 ∧ p2)) → p2) → p2)) → (p2 ∨ (True → (p4 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → (p2 → p1)) ∨ (((p4 ∧ p3) ∧ False) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (((p2 → p4) ∧ (p1 ∧ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h15 := h8 h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303910941159215449686531415912 : (p1 ∨ ((((p2 ∧ ((False ∧ p1) ∧ ((p2 ∨ (p3 → p2)) → p4))) ∧ True) ∨ (p1 ∨ ((p4 ∨ (p3 → p4)) ∨ (p2 ∨ (False → p3))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138691096081787274021077637133 : (((((False ∨ p5) ∧ (True → ((p1 → (p4 ∧ False)) ∧ p2))) ∧ ((((p1 → p1) ∨ (p3 ∧ p5)) ∨ p5) ∨ p4)) ∧ p4) → ((p2 ∧ p4) ∨ p3)) := by
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h14 := h7 h13
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- One of the premise coincides with the conclusion.
          exact h15
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h21 := h7 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h25 := h7 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h26
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314637960270898149453645949490 : (p3 ∨ (((((p5 → ((((False ∨ p3) ∨ (p1 → True)) → p4) → p4)) → p1) ∧ p2) ∧ p1) ∨ (p4 → (p5 ∨ (p4 ∨ (p5 ∧ (p3 ∧ p2))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133785415811172796202886162868 : (((((p5 → p4) ∨ False) ∧ ((((p4 ∨ p1) ∨ ((True → True) ∧ p2)) ∧ p3) → (((p4 ∧ p3) ∨ p5) ∨ False))) ∧ p3) ∨ ((True → False) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9734269778711829960814922080 : ((((True ∧ p2) → ((p4 ∨ p5) ∧ ((((p4 → (((True ∧ p1) → (p3 ∧ p2)) → False)) → p3) ∧ False) ∧ (p1 → (p4 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137641898396290812549550365208 : ((False ∨ (((p4 ∨ ((p4 → (p2 ∨ (p2 ∨ False))) → p5)) ∨ p4) ∨ (p1 ∧ (p2 ∧ ((False → p1) ∧ (p1 → False)))))) ∨ (False → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198528332382691809485773355737 : ((False ∨ ((False ∨ (True ∧ False)) ∧ (True ∨ p2))) ∨ (p4 → (((p4 → (False ∨ (p1 ∨ ((p5 ∧ False) ∨ (p2 ∧ p1))))) → p2) ∨ (p4 ∨ p5)))) := by
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
theorem thm_5_vars_191829959613640609089982715829 : ((p3 ∨ ((p3 ∨ ((True ∨ (p5 ∨ True)) → p5)) ∨ p5)) ∨ (((p5 ∧ ((p3 ∧ p4) ∧ (p1 ∨ p3))) → ((p1 → (p5 ∧ p3)) ∨ p2)) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116576553470551826851662371973 : (((p3 ∨ p3) ∧ ((((p1 ∨ (True ∨ p3)) → ((p5 → True) → (((p2 ∧ p2) → (p2 → True)) ∧ False))) ∨ (p2 → p3)) ∧ False)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178199889575951371229833106565 : (((True ∨ (p5 → ((p1 ∧ (False → p5)) → (False → (p4 ∧ p3))))) → p4) ∨ ((p1 ∧ ((((p5 ∧ False) → p2) ∨ (p3 ∨ False)) → False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∧ False) → p2) ∨ (p3 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759912253689038325972476956695 : (((p2 ∧ ((p4 ∧ ((p1 → p4) → (True → p1))) ∨ ((p1 ∨ (True ∧ ((True → ((True → (p1 ∨ p5)) → p5)) → p2))) → (True → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650211739208181423498513493065 : (((((((p5 ∧ p2) ∧ (p3 ∧ p2)) ∧ ((((p3 ∧ True) → p4) → (p3 → p5)) ∧ p1)) ∨ (((p1 ∨ p1) → p2) ∧ p4)) ∧ (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316993454344476628027502743580 : (p3 ∨ (p3 → ((((p2 ∨ (p2 ∧ (p2 ∨ p5))) ∧ p1) ∧ (p3 ∨ ((p4 ∨ True) ∧ (p2 ∧ p1)))) → ((True → (p4 ∨ p1)) ∧ (p5 → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h12.left
        let h18 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h26.left
          let h32 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h37.left
          let h40 := h37.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h37.left
          let h43 := h37.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h43
  -- Implications on the right can always be decomposed.
  intro h44
  -- Conjunctions on the left can always be decomposed.
  let h45 := h2.left
  let h46 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h47 := h45.left
  let h48 := h45.right
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h49 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h50 =>
      -- One of the premise coincides with the conclusion.
      exact h48
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h53.left
        let h56 := h53.right
        -- One of the premise coincides with the conclusion.
        exact h56
      case inr h57 =>
        -- Conjunctions on the left can always be decomposed.
        let h58 := h53.left
        let h59 := h53.right
        -- One of the premise coincides with the conclusion.
        exact h59
  case inr h60 =>
    -- Conjunctions on the left can always be decomposed.
    let h61 := h60.left
    let h62 := h60.right
    -- Disjunctions on the left can always be decomposed.
    cases h62
    case inl h63 =>
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h64 =>
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h65 =>
        -- Conjunctions on the left can always be decomposed.
        let h66 := h65.left
        let h67 := h65.right
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h68 =>
          -- Conjunctions on the left can always be decomposed.
          let h69 := h67.left
          let h70 := h67.right
          -- One of the premise coincides with the conclusion.
          exact h70
        case inr h71 =>
          -- Conjunctions on the left can always be decomposed.
          let h72 := h67.left
          let h73 := h67.right
          -- One of the premise coincides with the conclusion.
          exact h73
    case inr h74 =>
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h75 =>
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h76 =>
        -- Conjunctions on the left can always be decomposed.
        let h77 := h76.left
        let h78 := h76.right
        -- Disjunctions on the left can always be decomposed.
        cases h77
        case inl h79 =>
          -- Conjunctions on the left can always be decomposed.
          let h80 := h78.left
          let h81 := h78.right
          -- One of the premise coincides with the conclusion.
          exact h81
        case inr h82 =>
          -- Conjunctions on the left can always be decomposed.
          let h83 := h78.left
          let h84 := h78.right
          -- One of the premise coincides with the conclusion.
          exact h84



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157481724861383985068489565390 : (((((((p3 ∧ p1) ∧ p1) ∧ p3) → (p1 ∧ (p2 ∨ p1))) ∧ (p2 → (False ∨ p4))) ∨ (p5 ∨ p5)) ∨ (((p2 ∧ (p2 → p1)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609546968824453349612804574441 : (((((p3 ∧ ((((p4 ∨ False) ∧ (p4 ∧ ((p3 → (p3 ∧ p1)) ∧ p1))) ∨ False) ∧ ((p4 → p1) ∧ (p3 ∨ (p2 → True))))) ∨ p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662458098156845866256823128393 : (((((((p5 → (p2 ∨ p4)) → p5) ∨ p5) ∧ (((p1 ∧ p5) ∨ (((False → (p3 ∨ p4)) ∧ (p2 ∧ p4)) ∧ p3)) ∨ p3)) → (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350925841527651681676142713928 : (p4 → ((((False ∨ ((p3 → False) ∧ (p2 ∨ (((p2 ∨ p1) ∨ (((p1 → (True ∧ p4)) ∧ p5) → p3)) ∧ p4)))) ∧ p2) → p1) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825215715183620211102368858421 : (((((p2 → (p4 → True)) → (((((p4 → ((p4 ∧ ((((True ∧ p1) ∧ p3) ∧ False) ∧ p1)) ∨ p2)) ∧ True) ∨ p5) → p2) ∧ p2)) ∧ p1) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (p4 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299323058711870210433376890552 : (False ∨ (((((p3 ∧ p5) ∧ False) ∧ p5) ∧ (((p1 ∧ (p4 → (True → ((True ∧ p5) → ((p1 ∧ True) → (p2 ∨ True)))))) ∨ False) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64494223661312476862819045180 : ((p1 ∨ ((((True → (p4 ∨ ((False ∧ p5) → p2))) → (p1 ∧ False)) ∨ ((True → p2) ∨ True)) ∨ ((p4 → p1) → (p2 ∨ (True ∨ p1))))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242350081738983031990612670451 : ((p2 → p2) ∧ (p1 ∨ ((p2 ∧ (((p2 ∨ False) ∨ (False ∧ True)) ∧ (True ∧ ((p4 ∨ (p1 → (p3 ∧ (p5 → p3)))) → (p2 ∧ p1))))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430819459699334208878680637080 : (((((p2 ∨ p4) ∧ (True ∧ (((((True ∧ (p5 ∨ p5)) ∧ (True ∨ False)) ∨ (p5 ∨ True)) ∨ ((p3 ∨ p2) ∨ p3)) ∨ p1))) ∨ (True ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172155379187654462317590334343 : (((((((p2 → True) ∧ p4) ∨ (p3 → p2)) → p2) ∨ p2) ∨ ((p3 ∨ p3) ∨ False)) ∨ ((p4 → (p4 ∨ ((p3 → p2) → p1))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791941284873895130708134770383 : (((True → (((p2 ∧ True) → ((p2 → (((p5 ∧ (p1 ∨ ((p5 ∨ True) → (p4 ∨ (p2 ∧ True))))) → p3) → p5)) ∨ p3)) ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53165994402136214514645040668 : ((((p5 → ((((p2 ∨ p2) ∨ p5) ∨ p2) ∧ (p1 ∧ p5))) ∨ p4) ∨ ((p5 → (((((p1 → p2) ∧ p4) ∧ p3) → p3) ∧ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682627976996333959188399882626 : (((((((p3 ∨ True) ∨ False) ∨ (p2 → (False ∧ False))) → (p1 ∧ (p3 ∧ (p3 → (False → True))))) ∧ ((p3 ∧ p5) ∨ ((p5 ∧ p2) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22285434156405672600480638471 : ((((((p5 ∧ (p1 ∨ p4)) ∧ p5) ∨ p1) ∨ p5) → ((p3 ∨ True) → (((True ∨ p1) ∨ p4) ∧ (False ∨ (((p2 ∨ False) → p1) → True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h39
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- Conjunctions on the left can always be decomposed.
        let h45 := h43.left
        let h46 := h43.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h48
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h49 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h50
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h51 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h52
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h53 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h54
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63144250211061219890858094402 : ((p5 ∧ ((p4 ∨ ((True → ((p5 → (((p1 ∨ False) ∧ p2) ∧ p2)) ∧ p3)) ∧ (p5 ∨ (((False ∧ p4) ∨ (p4 → p1)) ∧ p5)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337125167870051676519220596465 : (p1 → ((p3 ∧ ((((((p3 → p5) ∨ False) ∨ (((p5 → True) ∧ (p1 ∨ p5)) → p2)) ∨ p4) ∧ ((p1 ∧ False) ∨ p1)) ∧ p5)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47728596745648859991309888533 : ((((((True ∨ (p4 ∨ (p3 → True))) → ((((p2 ∨ p4) ∨ p1) ∧ p1) ∧ (p4 ∨ (p3 ∨ p1)))) ∨ (p1 ∨ p2)) ∨ False) → (p2 ∨ p1)) ∨ p3) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h4 : (True ∨ (p4 ∨ (p3 → True))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h5 := h3 h4
      -- We need to get the left conjuct of h5 based on <expert-advice>.
      let h6 := h5.left
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159053681900541230215706283551 : ((p5 ∨ ((((p5 ∨ p1) ∨ (p4 ∧ (p1 ∨ ((p1 ∧ True) ∨ p4)))) ∧ p1) ∧ ((p1 ∧ p4) ∧ p1))) ∨ (((p3 ∧ True) → p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193264228839391969398924191060 : (((True → (False ∧ p1)) ∧ (p4 → (False → (p3 ∨ p2)))) → ((((((p5 ∧ (p4 ∨ (p3 ∧ p3))) → p4) ∧ True) ∧ p4) ∨ p2) ∨ (p4 → p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194042185506801948260533735292 : ((p5 ∨ ((p1 ∧ (p1 ∨ (p4 ∨ p1))) ∧ (True → p5))) → ((p4 ∨ (((False ∨ p4) ∨ ((((p5 → False) ∨ True) ∧ p5) ∨ True)) → p3)) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148990483444559549650765494130 : (((p3 ∨ (True ∨ False)) ∧ (p3 → ((((p2 ∧ True) ∨ (p1 ∧ p1)) → False) → ((p2 ∨ False) ∨ (p1 → False))))) ∨ ((p4 ∨ (p5 ∧ False)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ True) ∨ (p1 ∧ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62665668415607267276936703089 : ((p4 ∧ (((p5 → (p4 → (p2 ∧ ((p3 ∨ p5) ∧ False)))) ∨ (((p1 ∨ p5) ∧ True) ∨ (p3 ∨ (True → ((False ∧ p3) ∧ p1))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149196101644804412810012495020 : (((p4 → True) ∧ ((True → p5) → (p1 ∨ (((p2 ∨ p3) ∧ (p3 ∧ False)) ∨ (((p1 ∧ p5) ∧ p4) → p1))))) ∨ (((True ∧ p5) ∨ p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141469782138305168750092618509 : (((p3 ∧ (p3 → False)) ∧ (((True → ((((p2 → False) → ((p5 ∧ p4) → p1)) ∧ p3) ∧ False)) ∨ (p4 ∧ p1)) ∨ p3)) → (p5 ∨ (p4 ∨ p4))) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172003198247708358871780481073 : ((((p4 ∧ ((((p5 ∧ (p2 ∨ True)) ∨ p2) → p1) ∧ p3)) → p5) ∨ (True ∧ True)) ∨ ((False ∧ ((p1 ∧ p5) ∧ p1)) ∧ (p4 ∧ (p5 ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136018919987500675928982344383 : ((((((p4 ∧ (p4 ∨ p2)) ∧ False) ∨ (False → p1)) → False) → ((p3 ∧ (False → p5)) ∨ (p2 → ((False → p3) → p4)))) ∨ ((p2 ∧ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ (p4 ∨ p2)) ∧ False) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172674041274288214771461100526 : (((p4 → p2) ∧ ((p1 → False) → (p5 ∧ ((p2 → (p1 ∧ (True ∧ False))) ∨ p2)))) ∨ (((p5 ∧ p2) → p2) ∧ (p3 ∨ ((True ∨ True) ∧ True)))) := by
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
  exact h3
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
theorem thm_5_vars_263691331713028911630065314916 : (True ∧ ((((((((p5 ∨ p3) → True) ∨ p3) → p3) ∨ p4) ∧ (p2 ∨ p3)) ∧ ((p4 → p4) → p2)) ∨ ((False ∨ (p2 ∨ True)) ∨ (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_181685622885225746073335361251 : ((p4 → (False ∨ (True ∨ (True ∨ ((p4 ∧ p2) → (p5 ∨ (p1 ∧ p2))))))) → (((True → p4) ∧ p3) → (p4 ∧ (((p4 ∨ p2) → p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233314319258783375241323864373 : ((True ∨ (p5 ∨ p4)) → ((p3 ∧ True) → (False ∨ ((((p2 → p5) ∨ False) ∨ (False → (True → (((False ∧ False) → (p3 ∧ p4)) ∧ p3)))) ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- False on the left can always be used.
    apply False.elim h11
    -- False on the left can always be used.
    apply False.elim h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
      -- Conjunctions on the left can always be decomposed.
      let h22 := h19.left
      let h23 := h19.right
      -- False on the left can always be used.
      apply False.elim h22
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185758843453067687394054086366 : ((p4 → (((((False ∧ (False ∧ p1)) ∧ p1) ∨ p5) ∧ True) ∨ True)) ∨ (False ∧ ((((p5 ∧ (((True → p3) ∧ p1) ∨ p4)) ∧ p4) → p5) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197691115542167556520533850038 : (((p2 ∨ ((p2 → True) ∨ True)) → (p1 → False)) ∨ (True ∨ (((p1 ∨ ((False ∧ (((p4 → p3) → (p1 → p3)) ∨ p1)) → False)) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764925268549116920253727094509 : (((p4 ∧ (((p1 → (p4 → p3)) ∨ ((((p2 ∨ p4) → (False ∨ p5)) → ((p1 ∧ ((p1 ∧ False) ∨ (True ∧ p5))) ∧ p2)) → p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61777319058580535021527533303 : ((p2 ∧ ((((p3 ∨ False) ∨ ((False ∧ True) ∧ p3)) → ((p3 ∨ (p2 ∧ ((p2 ∧ ((False → (p1 → p4)) ∨ p2)) ∧ True))) → p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69030336524082747533553440117 : ((p5 → (((((False → (False → p5)) ∧ (((False → True) ∨ (p4 ∧ (True ∨ p1))) ∨ (p3 ∨ p2))) → ((p4 ∧ p1) → True)) → p1) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70699246243701762793961826929 : ((((((p2 ∧ (p4 ∨ ((p3 ∧ (p3 → p5)) → p2))) ∧ p5) ∧ (p5 ∨ (p5 ∨ p1))) ∧ (((p3 ∨ (p1 → p5)) → p4) → p2)) ∧ p3) → p5) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114621564482313550475976025374 : (((((((p2 ∧ ((True ∧ p3) ∧ True)) → p2) ∧ p1) ∨ ((p4 → False) ∧ p2)) ∧ p5) ∨ (p4 ∧ ((p4 ∨ p3) → (p3 ∨ p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230178231366293888816050259172 : (((p5 ∧ p1) ∧ True) → ((p1 ∨ p5) → ((((p5 ∨ p4) ∧ False) ∨ p2) ∨ ((p1 → (((p4 ∧ (True ∨ True)) ∧ (p1 ∧ p5)) ∧ p5)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62594830714572349697706995821 : ((p3 ∧ (p4 → ((((p2 ∨ ((p4 ∧ ((p2 ∨ True) → p2)) ∧ p5)) ∧ (False ∧ (((p1 ∨ False) ∨ (p1 ∨ False)) ∧ p2))) ∧ p4) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357266064184734981578212903353 : (p5 → ((p2 ∧ p5) ∨ ((((p2 ∧ ((p2 ∧ ((False ∧ False) ∨ p2)) → ((p3 ∧ ((True ∨ p1) → p5)) → p1))) → p1) ∨ True) ∨ (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118692345514241339479857199578 : ((p5 ∨ (((p4 ∧ ((False → p3) ∧ (False → (((p4 ∧ ((p5 ∧ p2) → True)) ∨ p1) → ((p3 ∧ p4) → p3))))) → p2) ∨ False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199481896351436173601351799588 : (((p3 ∨ (p1 ∨ ((p4 ∨ p1) → p5))) ∨ True) → ((((((p5 → p1) ∨ p4) ∨ p2) ∨ ((((p1 ∧ p4) ∧ False) → p2) ∧ p1)) ∨ p3) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62446249022071603721396022176 : ((p3 ∧ ((False ∨ (p3 ∧ True)) ∨ (((p1 ∨ False) ∨ ((p4 ∨ (((False ∧ p2) ∧ p4) → True)) → (((p1 ∧ p3) → p1) → True))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



