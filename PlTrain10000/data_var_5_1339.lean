variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194277078720612852780870338514 : ((p5 → ((p3 ∧ p2) ∨ (p4 ∨ ((p4 ∨ p3) → p1)))) → (((((False ∨ ((p4 ∨ False) → p1)) ∨ True) ∨ p4) → p5) ∨ (p2 ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215201002897033816301999758722 : ((True ∧ (p2 ∨ (p5 → p1))) ∨ ((p5 ∨ False) ∨ (p5 ∨ ((p1 → (True → (((p4 → True) ∧ p1) → False))) ∨ ((p5 ∧ (False ∧ p1)) → p1))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64803281499384916956756099057 : ((p2 ∨ ((False ∨ ((True ∧ (p3 → False)) ∧ (((((p2 ∧ (p4 → (p1 ∨ p2))) → p2) ∨ (p2 → p3)) → p3) ∨ (p5 ∨ True)))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49063080904755998956976384249 : (((((True → ((p5 ∨ p5) ∧ ((p2 → (False ∧ ((p1 ∨ p4) ∧ p3))) → True))) ∧ (p3 ∨ p2)) ∨ (p4 ∨ p1)) ∨ (p4 ∧ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_519885584802303751222751571655 : ((((p2 ∨ p2) → (((True ∧ (False ∧ ((((p4 → (((False ∨ True) ∧ p1) → False)) → (True ∨ p5)) → (p3 ∨ p2)) ∧ p5))) ∨ p2) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169612871103246120135918948568 : ((((((((p1 ∨ False) ∧ True) → (p2 ∨ p5)) ∨ (True ∨ p5)) ∧ True) → p4) → p4) ∧ ((False ∨ (((p4 → p1) ∧ (True → p2)) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∨ False) ∧ True) → (p2 ∨ p5)) ∨ (True ∨ p5)) ∧ True) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757281844867597417276262712099 : (((p1 ∧ ((p2 ∧ p1) ∨ (((((p3 ∨ (p1 ∧ p4)) ∨ False) ∧ ((True → (p4 → p5)) ∧ (((p1 ∨ p4) ∧ p3) → p3))) ∧ p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684255938888697194198193597408 : ((((((((True ∨ p4) ∧ p5) ∧ p5) ∨ ((p3 → (p1 ∨ False)) ∧ p3)) ∧ ((p1 → p1) ∨ p1)) ∨ ((True → p3) → (True → (p3 ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687669067603237370707301153517 : (((((p5 ∨ (p1 ∧ (p2 ∨ (p3 ∨ (((True → p1) → p3) ∨ (p2 ∨ p4)))))) → p3) ∧ (((p3 ∨ p2) ∨ p5) ∧ ((p5 → p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353402466740540767827855379235 : (p4 → (False ∨ (p4 → ((((p4 ∧ p1) ∨ ((p3 ∨ False) ∧ ((p5 → True) → p5))) ∨ (True → (p4 ∨ (True ∨ (p5 → True))))) ∨ (p1 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308547527049268330010116137646 : (p2 ∨ ((((True ∨ True) ∧ (False → ((p4 ∨ p4) → (True ∨ True)))) → (((p3 ∧ ((p3 ∨ True) ∨ p1)) ∧ ((p1 ∧ True) → p5)) ∨ True)) ∨ p3)) := by
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
  cases h2
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
theorem thm_5_vars_115417019998407288471360053215 : (((((p1 → ((p4 ∨ True) → p1)) ∨ p4) ∧ p2) ∨ (p1 ∧ (((p4 ∧ (p2 → (p1 ∧ True))) ∧ p3) ∧ (p3 ∧ (p1 ∨ p1))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117092726990851920489161308622 : (((p1 → p1) → (p3 ∨ ((p2 ∨ (((p4 → p1) → (((p5 ∧ p2) ∧ ((p5 ∧ p1) → p2)) ∧ False)) ∨ p5)) ∨ (p1 → True)))) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44475772512046707009740401602 : (((((p3 ∨ (p2 ∨ p5)) ∧ (((p2 ∨ (p4 ∨ p5)) ∨ p4) ∧ p2)) → (((p4 ∨ (p1 ∧ p2)) ∨ (p1 → p4)) ∨ (p4 ∨ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789141152514804009299186207918 : (((p5 ∨ ((True ∧ (((((False → (p5 ∧ (p4 ∨ p3))) → p5) ∧ p5) ∧ (p1 ∧ (p4 → (p1 ∧ p2)))) → p2)) ∨ (p3 ∨ (p3 ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656402077774780646091015344146 : ((((((((True ∨ p2) ∨ (p4 → p3)) → p5) ∧ (p4 ∨ p4)) ∧ (False ∨ (p1 → (p5 → ((p5 ∨ p2) → (p3 ∨ True)))))) ∨ (p4 → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354814127757683317176518964331 : (p5 → ((((p1 ∧ p4) ∨ p2) ∧ (p4 → (((p4 ∧ p2) ∧ ((True ∧ (((p4 → True) → p2) ∨ (p5 → p1))) ∨ p3)) ∨ (p1 ∧ False)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788484084678808097288613718254 : (((p5 ∨ ((True ∧ (((p3 ∧ p3) ∨ ((p4 → True) → True)) ∧ ((False ∨ (False ∨ (((p1 → (p2 → p2)) → False) → p5))) ∨ p2))) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p2 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200661064640132263133923072816 : ((p1 ∧ ((p4 → (p1 ∨ p1)) ∨ (p4 ∨ p5))) → (((p3 → p3) → p5) ∨ (p1 → ((p2 ∨ (p5 → ((p4 → True) ∨ (p2 → False)))) ∨ True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351001108964171408408810513801 : (p4 → ((False ∨ (((p4 ∧ True) ∧ ((p3 ∧ ((p3 → ((False ∨ p3) ∨ p5)) ∨ True)) ∨ (p2 → (p1 ∨ p4)))) → (True ∧ False))) ∨ (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64225508593951885955598393731 : ((False ∨ (p5 ∧ ((p5 → p2) ∨ ((p3 ∨ ((p4 ∧ ((p1 ∨ (((p5 → (p2 ∨ p2)) ∨ p4) ∨ True)) → p1)) ∧ (p4 ∨ True))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60425659507818681159369190471 : (((p4 → p3) → ((((p3 ∨ (p3 ∨ ((p5 ∨ ((p3 ∧ True) ∧ (p5 ∧ p4))) ∨ (p3 ∨ (p5 → p5))))) ∨ p2) → p4) → (p5 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753151840137881137774701057905 : (((False ∧ (((((p1 ∨ p4) ∧ (p4 ∧ (True ∧ ((True ∨ True) → (((p2 → p3) ∧ p5) → p4))))) ∧ p5) → (p5 → p2)) ∧ (p3 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147689793888563869886681698922 : ((((True ∧ ((p4 ∨ (p4 ∨ (p1 → (False ∨ p5)))) ∧ (True ∨ (p3 → p4)))) → (True ∧ (p2 ∨ p2))) → p4) ∨ (p4 → ((p1 → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607926650609227563510900967439 : (((((p1 → ((((p5 ∧ p2) → (p5 ∨ False)) ∧ (((p2 → p1) ∨ p4) ∨ (p3 ∨ True))) → (p5 ∧ (True ∧ (True ∨ p2))))) ∧ p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60432099772770577245897149968 : (((p4 → p4) → (((((p2 ∨ p2) → True) → (False ∧ p1)) ∧ (p5 ∧ (p5 ∨ p1))) → (((p5 ∧ p4) ∨ p2) ∨ (True ∧ (False ∨ False))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∨ p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : ((p2 ∨ p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622013249777346867163823766744 : ((((p2 ∧ ((((False ∨ p5) ∨ ((p1 → p3) ∨ (((p2 → p4) ∨ p4) ∧ (p2 ∧ (((p3 ∨ False) → p5) ∨ p5))))) ∧ True) ∨ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168810520956760079589829415695 : ((p2 ∨ (((False ∨ True) ∧ (False ∧ p2)) ∨ (((True ∧ True) → (p4 ∨ (p5 → p1))) ∨ True))) → ((p2 → False) → (((p4 → p4) → p5) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h12 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616940660057801965039221608989 : (((((True ∨ ((p5 ∧ (((p5 → False) ∧ p4) ∧ True)) ∨ False)) → ((p5 ∧ True) ∨ ((p1 → (p5 ∧ (p1 ∨ True))) ∨ (False ∨ p4)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704626778233209876606358127590 : (((((True → p3) → ((p1 ∧ True) ∧ (False ∧ (True ∧ p2)))) → (p2 → ((p4 → True) → (((p5 → p2) ∧ ((p3 ∧ False) ∨ p1)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159180012222158351684524306297 : ((p1 → (p2 ∧ ((p5 ∧ ((p2 ∨ ((p3 ∨ ((p3 → (p1 ∧ p3)) ∧ p2)) ∨ p3)) ∨ True)) → p4))) ∨ (((p3 ∧ False) ∨ False) → (p3 → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672956902814464978756411698109 : ((((((True ∨ (((((p3 ∨ False) ∨ p2) → p1) ∨ p3) → p2)) ∨ (False ∨ p1)) ∧ (p5 ∨ (p2 ∨ (True ∧ True)))) → ((p2 ∧ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657676825101060788991821397572 : (((((p5 ∨ p5) → ((p4 → False) ∨ ((((True → True) ∧ False) ∨ (p4 → (p1 ∨ p2))) ∨ ((p3 ∨ (p2 → False)) ∧ p3)))) ∨ (True ∨ p5)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_1821471793756955202782455820 : ((p3 → (p2 ∨ (((((p5 → p5) ∧ (p3 ∨ (p4 → True))) ∧ True) → p2) ∨ ((p2 ∧ p3) ∨ (False ∨ False))))) ∨ (p5 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792971726151371388994929438903 : (((True → ((p4 → True) ∧ ((p4 ∨ (((p3 ∧ (p2 → p1)) → p2) → ((False ∨ p5) → True))) → (((p2 → p1) → p2) ∨ (p3 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152205901528901738437575883419 : (((((p5 ∨ (p5 ∧ p4)) ∨ p1) ∨ p5) ∧ (((p5 → (((p4 ∧ p4) ∨ (p4 → False)) ∧ p1)) → p4) → p1)) → (((p3 ∧ False) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64350135720397495347336407835 : ((p1 ∨ (((((((p3 → (p5 ∧ True)) ∨ (p3 → ((p5 → True) ∨ p4))) → ((p4 ∨ True) ∧ p4)) ∧ True) ∨ (p1 ∨ p1)) ∨ False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116795916184250801987801209632 : (((p2 ∨ p2) ∨ ((True ∧ (((((p1 ∧ (p3 → p3)) ∧ p4) ∨ (((False ∧ False) → True) ∧ p5)) → p4) ∨ p3)) → (p4 ∨ p3))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165584972180245130942053578584 : (((False ∨ ((p2 → (False ∨ p4)) ∨ (p2 ∨ p3))) ∨ (False → (((p3 ∨ p1) → p5) ∨ p3))) ∨ (p5 → ((((p5 ∨ p5) ∨ p2) → p4) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111667762586892583446340280644 : ((((p4 ∨ (((((((False ∧ (p2 → False)) ∨ (False ∨ p4)) ∧ p2) → p1) ∧ p4) ∨ (True ∨ p1)) → (p5 ∧ p2))) ∨ True) ∨ p2) ∨ (True ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49768344174066005679661489892 : (((p1 ∨ ((((((p1 ∧ (False ∨ p4)) ∨ ((True → p2) ∧ False)) ∧ p1) → p5) → (True ∨ (p2 → p4))) → True)) → (p5 → (False ∨ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_668835211231342158207781485825 : ((((((((p5 ∧ p1) → (True → True)) ∨ (True ∧ p4)) → (((p3 ∨ (True → p4)) → p2) → (p1 → p2))) ∨ p2) ∨ ((False ∧ False) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_191587961326755853937281474131 : ((p2 ∧ (p4 ∧ (((p4 → (p2 ∧ p5)) ∨ p5) ∨ False))) ∨ (True ∧ (p3 ∨ (True ∨ (p4 → ((p3 → p5) ∨ ((p1 ∨ (p4 → True)) → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675726528042381099804423214143 : (((((p2 ∧ (True ∧ (((p5 → p3) → (False ∨ (False ∧ (p4 → p1)))) ∨ p3))) ∧ ((False ∧ False) ∨ p2)) ∧ ((p2 ∨ p2) → (False → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172625785626657850252772459898 : (((p2 ∧ p2) ∧ (((((p1 ∧ ((True ∧ p5) ∨ p1)) ∧ p2) ∧ p4) ∧ p2) ∨ p1)) ∨ (p4 → (((False → False) ∨ p1) ∨ ((True ∨ p5) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51358684977733834113297522897 : (((((((True ∧ p4) ∨ p3) → (p1 ∨ p3)) ∨ (p1 ∨ (p1 ∧ (p4 ∧ (True → p4))))) ∧ p2) → (p4 → ((p3 ∨ p1) ∨ (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61130307569351691308324254785 : ((False ∧ ((((p5 ∨ ((p3 ∧ p3) → p4)) → p2) ∨ p5) ∨ ((((p4 → p2) ∨ p2) ∨ ((p2 → p4) ∧ (p2 → p1))) ∨ (p5 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318899715543783709871670008207 : (p4 ∨ ((p1 ∨ ((((False ∧ p1) → ((p1 ∨ p4) ∧ p5)) ∧ ((p1 → (False → p2)) ∧ p4)) → ((p5 → p1) ∨ p4))) ∨ ((False → True) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46377371005915158224723587824 : (((((p3 ∨ (((True ∨ True) → (p3 → p1)) → p2)) ∧ p4) ∧ (((p5 → (False ∨ (True → (True → p5)))) → True) → p1)) ∧ (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42164023538289475499346021163 : ((((p4 → False) → (((p2 → (((p2 ∧ p4) ∧ False) → ((False ∨ p3) ∧ (((True → p2) ∨ p5) ∧ (p2 → False))))) → p5) ∧ p3)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783014898216458474063210148736 : (((p3 ∨ (((p3 ∨ p5) → ((True ∨ ((p2 → False) ∨ (p3 → (p1 ∧ (((p4 ∧ (p3 → p4)) → p3) ∧ p4))))) → p2)) ∨ (True ∨ p3))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134175934338712798269400353600 : (((((False ∨ (((p1 ∧ p3) → p4) ∨ p3)) → ((True ∨ p3) ∨ (p2 ∧ False))) → (p4 ∧ (p4 ∧ (p4 ∧ p4)))) ∨ p5) ∨ ((False → p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313200062538854929675234098529 : (p3 ∨ (((p1 ∨ ((p3 ∧ p2) ∧ p1)) ∨ (True → (p2 ∨ ((p4 ∨ ((p5 ∧ p1) ∧ (p3 → (p5 ∧ p3)))) → ((p2 ∧ p1) → p2))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713093105126088350017614942332 : ((((p5 ∧ ((p3 ∨ p3) ∨ (True ∨ p3))) ∨ ((False ∨ ((True ∧ ((True ∧ (True → p1)) ∧ (p5 → p4))) ∨ p2)) ∨ (False → (p2 → p1)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_178032633308114970395430076748 : (((p5 → ((p1 → (p4 ∧ (False ∨ p3))) → ((p3 ∨ True) → False))) ∨ p1) ∨ (p1 ∨ (((p1 ∨ p5) ∨ (False → (p5 → (True → p1)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310033505574143848450266448268 : (p2 ∨ (((True ∨ (p4 → p1)) ∧ ((False → (p3 → p2)) → (((p5 ∧ p1) → True) → p4))) ∨ ((p3 → p4) ∨ (p5 ∨ (p4 → (p2 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329350478433712117703948517542 : (True → (((p4 ∨ p5) → p4) → (((((p2 → (p2 ∨ True)) → False) ∧ ((p4 ∨ p3) → False)) ∧ p2) → (p5 ∧ ((p1 → (p3 ∧ p1)) ∨ False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (p2 → (p2 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h3.left
  let h12 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (p2 → (p2 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h17 := h13 h15
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135363816408591041065930345672 : (((p4 → (((p5 ∨ (((p2 ∧ p4) ∧ p4) → (p4 ∧ ((p5 → True) → p5)))) ∨ True) ∧ p4)) ∧ (p1 ∧ (True ∧ p5))) ∨ (p3 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138288551209223355403724130131 : ((p3 → ((p4 ∧ ((((p3 ∨ p1) → p2) → p2) ∨ (((True ∨ (p1 ∧ ((p4 ∨ p5) ∨ p2))) → p2) ∨ p3))) → False)) ∨ ((p2 ∧ False) → p2)) := by
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
theorem thm_5_vars_166505409302789424316887107169 : ((p4 ∨ ((True ∧ ((((False ∨ True) ∧ (True ∨ True)) → True) → (p3 ∨ (p3 → p3)))) ∧ p1)) ∨ (p2 → (((p5 ∨ p3) ∨ (False ∨ True)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40949566989881114481005651127 : (((((((False ∧ ((p2 → p2) ∧ ((p4 ∧ (p1 ∧ (True ∨ p5))) → True))) ∧ (False ∨ p3)) ∨ p3) ∨ (False ∨ p5)) ∨ (True ∨ p3)) ∨ p5) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148179574672364663366359890390 : ((((p2 ∨ ((p5 → (p5 ∧ (p4 → ((False ∧ p2) → p1)))) → p4)) ∧ (p3 ∧ True)) ∧ ((True ∨ p3) ∧ p1)) ∨ (True ∨ (True ∧ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168386789518038752807022139482 : (((p1 → p1) ∨ ((p2 ∨ (p1 → (p5 ∧ p3))) ∧ (False ∨ (p2 → ((p4 → p5) ∧ p5))))) → (((False ∧ p4) ∧ p3) ∨ (False → (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h14
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340984168668536653765547717339 : (p2 → (((p5 → p1) ∨ (((True ∧ (True → (p3 ∨ ((p1 → (p3 ∨ p1)) ∧ (p5 ∨ p2))))) ∧ (p4 ∨ (False ∧ (p2 → p3)))) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197544936769492786695439526289 : ((((p2 ∨ (True ∧ p3)) ∨ False) ∨ (p3 ∧ False)) ∨ ((((p4 ∨ True) ∧ p3) → (p1 ∨ (True ∨ (((p2 ∨ (p5 → p4)) → True) → p1)))) ∨ p1)) := by
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
  cases h2
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
theorem thm_5_vars_300884491538847764553356696135 : (False ∨ (((p2 → p2) → ((False → p5) ∧ ((True → ((p5 → p1) → p5)) → p3))) ∨ (p4 → ((((p1 ∨ p3) ∧ p4) ∧ p5) → (p5 ∨ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
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
theorem thm_5_vars_39961795076365591517645499257 : (((p4 → ((False ∨ ((p1 → (p5 ∨ (p5 → (p5 ∨ p2)))) → (p5 → p3))) ∨ ((p2 → ((p1 ∨ False) ∨ (True ∧ False))) ∧ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67658471527172171864068239494 : ((p1 → (p4 ∨ ((True ∨ (p3 ∨ ((((p1 → p4) ∨ False) → p3) ∧ (True → ((p2 → (False → p4)) ∨ p5))))) → ((p4 ∧ p5) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655676429637443876415145394261 : ((((((((True → p3) ∧ p5) ∨ (False ∧ (((p2 ∧ p4) → p4) ∧ p4))) → ((p1 ∨ True) ∧ p3)) ∧ ((False → p3) → False)) ∨ (p1 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_143799466961339250916490205437 : (((((p3 ∨ (p4 ∨ ((p2 → True) → (True ∨ ((p3 ∨ p5) ∧ False))))) ∧ ((p5 ∨ True) ∧ p5)) ∨ True) ∨ p5) ∧ (p3 ∨ ((True ∨ True) ∧ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158918474061984264341858461366 : ((p1 ∨ (p2 ∧ ((True → (p1 ∨ ((False ∧ False) ∧ (p1 → p3)))) ∨ (((p5 ∨ p4) ∧ p3) → p5)))) ∨ ((False ∨ ((p3 ∨ p5) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197982813591676922746621167981 : (((p2 ∨ p5) ∧ (((p2 ∧ p2) ∧ p3) ∨ p5)) ∨ (((((p1 → (False ∨ p4)) ∧ p4) ∧ True) → ((p1 → ((True ∨ False) → p1)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184155273106770274116760471087 : (((p2 ∨ (p3 ∧ (p3 ∧ (((p3 ∨ p3) ∨ p4) ∨ p1)))) ∨ True) ∨ ((((p4 ∨ p3) ∨ p3) ∨ ((p2 ∧ (p1 ∧ p4)) ∨ (p4 ∨ p3))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324642687187992069813042400610 : (p5 ∨ (((p4 → p2) ∧ p2) ∨ ((True → ((p2 ∧ (p4 ∧ p4)) → ((((False ∧ (p2 → p5)) ∨ p1) ∨ p2) ∨ p5))) ∧ ((p3 ∨ p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174620980567038688045908635139 : ((((False ∧ (False ∨ p5)) → p2) → ((p3 → (((True ∨ True) ∨ p4) ∧ p2)) ∧ False)) → (p2 → (p2 → ((p4 ∨ p5) ∧ ((p5 → p2) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ (False ∨ p5)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40633553144940655869142145305 : (((((((p4 ∨ (((p1 ∧ ((((False ∧ p5) → True) → p5) ∧ p5)) ∨ p4) ∧ p3)) ∧ True) ∧ (p4 ∧ (p4 ∧ p2))) → p5) → p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352839257461143352813799509338 : (p4 → ((p2 → p4) → (((False ∨ p1) → True) ∧ ((((True → True) ∧ ((((p2 → p2) ∨ False) → p2) ∨ p1)) ∧ True) ∨ ((p3 ∨ p4) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257548498027532398880458794746 : ((p3 ∨ p1) → ((((False ∨ p3) ∧ (((True → (p5 ∧ ((False → (p3 ∧ False)) ∨ p4))) ∨ ((p3 → p5) ∨ (True ∧ True))) → p1)) ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_319038775881857686280074125416 : (p4 ∨ (((p4 → (((p5 ∧ (p3 ∨ (p3 ∧ True))) ∨ (False ∨ p2)) ∧ (p5 ∨ (p3 ∨ p2)))) ∨ (False → False)) ∨ ((p4 ∧ (p2 ∧ p4)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258580762934699702442585289270 : ((p5 ∨ p4) → ((((((p3 → True) ∧ (((False ∧ (p5 → p2)) ∨ (False ∨ (p4 ∧ False))) ∧ p1)) ∨ p3) ∨ (True ∧ (True ∨ p5))) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165035096639324597908221082895 : ((((p3 → (False → p2)) → (((p2 ∨ (p5 ∧ p2)) ∧ (p2 ∧ (p2 ∧ False))) ∧ True)) → p3) ∨ (((p4 ∧ p4) ∨ p3) ∧ ((p1 ∧ p4) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (False → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321820421976126707170261073062 : (p5 ∨ (((((p5 ∧ p4) ∨ (((p3 → p1) → p3) ∨ ((True → (p5 → (((p4 ∧ p1) → p4) ∧ p5))) ∨ (p2 → p5)))) → False) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_40760049716949120547911205786 : (((((p1 ∨ p5) ∨ (p4 → (((p2 ∨ ((p5 → True) ∨ p2)) ∧ ((p2 ∧ ((p3 ∧ (False ∨ p1)) ∨ p5)) ∧ False)) ∧ True))) → p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350279400871217011402970645280 : (p4 → ((p5 ∧ ((True → p5) → ((p4 ∧ (False ∧ (p4 → p5))) ∨ (p3 ∨ ((p4 → (((False ∧ p1) ∨ p3) → (p5 ∧ p1))) ∨ p3))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328779333581041017266762008027 : (True → ((p5 → ((False ∨ ((p3 ∨ (p3 ∧ p4)) → True)) ∨ False)) ∧ ((p4 → False) → ((p3 ∨ ((p4 ∧ (p4 → p2)) ∨ (p2 ∧ p2))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60768081262624478080371226555 : ((True ∧ ((p4 ∧ p5) ∨ (((((True ∧ False) → (p1 → p4)) → False) ∧ True) → ((p4 ∧ p2) ∧ ((True ∧ (p4 ∧ p5)) ∧ (p3 → p3)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ False) → (p1 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : ((True ∧ False) → (p1 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h17 := h10 h12
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h20 : ((True ∧ False) → (p1 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- False on the left can always be used.
    apply False.elim h24
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h25 := h18 h20
  -- False on the left can always be used.
  apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
  have h28 : ((True ∧ False) → (p1 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- False on the left can always be used.
    apply False.elim h32
  -- We have shown the premise of h26, we can now drive its conclusion.
  let h33 := h26 h28
  -- False on the left can always be used.
  apply False.elim h33
  -- Implications on the right can always be decomposed.
  intro h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804560900133407517317663520956 : (((p3 → (((False → (p2 ∨ (False → p1))) ∨ True) → ((True ∨ p2) ∧ ((p4 → (p4 ∧ False)) → ((p2 → (False → p2)) → (p1 → p1)))))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742416885388897976580356051123 : ((((p1 → p5) ∨ ((((p3 ∨ p5) → (p3 ∨ p3)) ∨ p4) ∧ (((p1 ∨ (True → (False ∨ (p1 ∧ (p3 → (True ∧ p2)))))) ∧ False) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_401411653109868377530158114447 : (((((((p1 → (p1 ∨ p5)) → (p3 → (p1 ∨ p1))) ∧ ((p2 → ((p2 ∧ (p4 ∨ False)) ∧ (p3 → (False ∨ False)))) ∧ p2)) ∧ True) → p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68150365229647772570341055570 : ((p3 → (((((False → p2) → True) ∧ (False ∧ (p3 ∧ (p2 ∧ (False ∧ p4))))) ∧ ((p2 ∧ ((p3 → True) → (p5 ∨ p5))) ∧ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355540034858546262296549019287 : (p5 → ((((False → ((True → (((p5 ∧ ((p4 ∧ p2) ∧ ((p4 → p1) ∧ (p4 ∧ p5)))) ∧ p2) ∧ False)) ∧ p3)) → p2) ∨ p1) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198692761219591560221652057989 : ((p4 ∨ (False ∨ (True ∧ ((p5 → True) → p5)))) ∨ (p3 → (((((p4 ∨ p3) → p2) → ((True ∧ p1) ∧ p3)) ∨ (p5 ∨ p3)) ∨ (False ∧ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324158436703790082351715339720 : (p5 ∨ ((((True ∨ False) ∧ ((p2 → (p5 ∧ p2)) → p5)) ∧ p5) ∨ (True → (False → (p5 → ((p5 ∧ (((p3 ∨ True) ∧ p4) ∨ p5)) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h2
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244880472690489448972819750097 : ((p1 ∧ p2) ∨ (((((p3 ∨ p4) → p3) ∨ (p2 ∨ p1)) → (False ∧ p1)) ∨ (((p1 ∧ (p1 → p1)) → ((False ∧ False) → (p2 → p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52509279508514811874037965383 : (((((((p3 ∧ p1) → p3) ∧ p3) ∧ ((p5 ∨ (False ∧ p2)) ∧ p2)) ∧ p5) ∨ ((p2 → (((False → False) ∧ True) ∨ p4)) ∨ (p2 ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299173866480343716484538585628 : (False ∨ ((((p5 ∨ ((((False → (((p4 ∧ p3) ∨ p2) → p2)) ∧ p1) ∨ (p2 ∨ False)) ∧ (p3 ∨ (p3 ∨ p3)))) → (p5 ∨ p1)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37539619899769068139168696341 : ((((p4 ∧ ((((True → (p4 → ((True ∧ (p1 → p4)) → (True ∨ p5)))) → p1) → (True ∧ p4)) ∨ (p4 ∨ (False ∧ False)))) ∨ p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115388850878867026535300827384 : ((((False ∨ p4) ∨ (((p4 ∨ p1) ∨ False) ∧ True)) ∧ ((((((p2 → p2) ∧ (False → True)) → p3) → (p3 ∧ p4)) ∧ p1) → p1)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123900889517387387523764950684 : (((((False ∧ (p1 ∨ (False ∨ p5))) → (p4 ∧ (p2 ∧ False))) ∧ p3) ∧ (((p1 ∨ p3) ∨ (((p4 → False) → p3) → p4)) → p1)) → (p2 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ p3) ∨ (((p4 → False) → p3) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651628405571166096604499399704 : (((((p4 → p5) ∧ (((p4 ∨ ((p2 → (((p3 ∧ p2) ∧ p2) ∨ (((False ∧ False) ∧ True) ∨ p3))) ∨ p3)) ∨ False) ∨ p5)) ∧ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



