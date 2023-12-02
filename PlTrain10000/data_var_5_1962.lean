variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789243347002523822139138691451 : (((p5 ∨ (((p4 ∧ (p2 ∧ (False ∧ ((p4 ∧ p2) ∨ p3)))) ∨ (p3 → (p3 → (p5 → (p5 ∨ False))))) ∨ ((p2 ∧ p2) ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50802316069210460787376760605 : (((p1 → ((((((p4 → p5) → p3) ∧ (p3 → p5)) → (p5 ∧ False)) → p2) ∨ ((p3 → p2) → False))) → (p1 ∨ ((p5 ∧ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40444936282888239078539332343 : ((((((((p2 ∧ p2) ∨ True) ∨ p4) ∧ False) ∧ (p3 ∨ (True ∨ (((p2 ∧ (p1 ∨ False)) ∧ p5) → ((p1 → False) → p3))))) ∨ p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53744278298507724287590621503 : ((((((p4 ∧ ((False ∨ p3) ∨ True)) ∨ False) ∧ False) ∧ p2) ∨ ((p4 → ((p1 → p4) → True)) ∨ ((p3 ∨ ((p1 ∨ p1) ∧ p4)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47114979968346752659046425971 : ((((((p5 ∧ p5) ∨ (((p5 ∨ p2) ∨ False) → False)) ∧ (p2 → (p4 ∧ (p2 → (p3 → p2))))) ∨ ((p1 ∨ True) ∨ p4)) ∨ (True → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_678240030932644311168343549299 : ((((((False → (((p5 → p4) ∨ p3) ∧ False)) ∨ (p2 ∨ p1)) → ((p1 ∨ False) ∨ (p4 ∧ (p5 ∧ p4)))) ∨ (p5 ∨ (p4 ∨ (p5 → True)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49739441515903521424781552296 : (((p3 ∧ (((p5 ∨ p1) → p1) ∧ ((((((True → p2) → p3) ∨ False) → p4) → ((p5 → p5) → p4)) ∧ p2))) → ((p2 ∧ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322364359149505115773566897078 : (p5 ∨ ((((True → p5) → (p1 ∧ (True ∨ (True ∨ ((p4 ∧ p3) → ((False → (p2 ∨ p2)) ∨ (False ∨ True))))))) → ((True → False) → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135056592795622877616679526008 : (((((p1 ∨ (((p5 ∧ ((p5 → p2) ∧ False)) ∨ ((p3 ∧ (True ∨ False)) ∧ True)) → p5)) ∨ p4) → p2) ∨ (p1 ∨ True)) ∨ (True ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232370867497793051920117646502 : (((p5 → True) → True) → ((((True ∧ ((p2 → (False ∨ False)) ∧ (False ∨ False))) → p3) → (True → ((False ∨ (p1 → (p3 → p2))) ∧ False))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ ((p2 → (False ∨ False)) ∧ (False ∨ False))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h3
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687468493703462468270682164588 : ((((((False ∧ p2) ∧ ((p1 ∧ (True → (False ∧ False))) ∨ (p1 → (p4 ∨ p4)))) ∨ True) ∧ ((((p5 ∨ (False ∨ p5)) → p4) → p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255543577771177736011898790532 : ((p5 ∧ p3) → ((((((p5 ∧ (p1 ∧ (p2 ∨ (p3 ∨ p1)))) ∨ p2) ∧ ((p1 ∨ p4) ∧ ((p1 → False) ∧ (False ∧ False)))) ∧ p3) ∧ p4) ∨ p3)) := by
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
theorem thm_5_vars_193957010536136905430603094438 : ((p2 ∨ (p3 ∧ ((True ∧ (p1 ∨ (p5 ∨ p4))) → False))) → (((p4 → p5) ∨ ((((p5 → True) ∧ (p1 ∨ (p2 ∧ p5))) → True) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_76936923818653424928135664521 : ((((((((p2 → p5) ∨ False) ∨ p4) ∧ p2) → False) ∨ ((p3 ∨ (p3 ∨ p4)) ∨ (True ∨ ((p5 ∨ (False ∨ (p5 → False))) ∨ p4)))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p2 → p5) ∨ False) ∨ p4) ∧ p2) → False) ∨ ((p3 ∨ (p3 ∨ p4)) ∨ (True ∨ ((p5 ∨ (False ∨ (p5 → False))) ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52029812239477046220478137293 : (((p2 ∨ (p2 ∨ (((((False → p3) ∧ (p2 ∧ p5)) ∧ p3) ∧ (True → p1)) ∧ p1))) ∨ ((((True ∨ False) ∧ (False ∧ p3)) ∨ p1) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310244334293348503525625586823 : (p2 ∨ (((p3 → (p2 → p1)) ∧ ((True ∧ (p4 → True)) ∧ (p5 ∧ p5))) → (p3 → (((True → (((p4 ∨ p3) → True) ∧ p2)) → p1) ∧ True)))) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h15 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h16 := h4 h15
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- One of the premise coincides with the conclusion.
  exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9465821977246081585411235851 : (((((p3 ∨ p3) → p5) ∧ ((p4 ∧ ((p2 → (p2 ∧ True)) ∨ False)) ∧ (p4 ∨ ((((p3 → (p2 ∨ p1)) ∨ False) ∧ p4) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218110162560604589137117524630 : (((p1 → p2) ∧ (True → False)) → ((p1 ∨ ((True ∨ (p3 → (((p3 ∨ p3) ∧ (p4 ∨ p4)) ∨ (((p2 → True) ∧ p3) → False)))) → p5)) ∧ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316560850744485255283006714226 : (p3 ∨ (p3 ∨ ((p2 → (p3 ∨ ((p3 ∨ (p5 ∧ (p2 ∧ p3))) ∨ (p5 → (p2 ∨ (p1 → ((p1 ∧ (p3 ∨ p2)) ∨ p3))))))) ∨ (p5 ∧ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111849663268204781083775480417 : (((((p3 ∨ ((p5 ∧ p3) ∨ (False ∧ ((p1 ∧ False) ∧ p4)))) ∧ (p3 → (True ∧ (True ∨ p3)))) → ((True → p5) ∧ p4)) ∨ True) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303759121120790065662169575173 : (p1 ∨ (((((p5 ∨ (p5 → (((p2 ∨ (p2 ∧ p2)) → True) ∧ p1))) → (True ∨ (p4 ∨ (p1 ∨ p4)))) → (p3 ∧ (p2 ∧ True))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148497515396844654080115936771 : ((((p4 ∧ p3) ∧ ((True ∧ (p2 ∨ p1)) ∨ ((p3 ∨ False) ∧ p3))) ∨ (False ∨ ((p1 ∧ (p3 → p4)) ∨ p5))) ∨ (p1 → (p2 → (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302994786809054051502761172920 : (False ∨ (p1 → ((((p1 ∧ p5) → p5) ∧ (p4 ∨ (((p3 ∨ (p5 → ((p3 → (p3 ∨ True)) ∨ (p1 → p1)))) ∨ True) → p5))) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208202958522650869243601195803 : (((True → (p1 → p1)) → (p4 ∨ p4)) → ((p4 ∨ ((True ∨ (p2 ∨ True)) → p3)) ∨ ((((((p1 ∨ p1) ∧ p4) ∨ p3) ∧ p5) ∧ p2) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p1 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219531229709464536883829103938 : ((p5 ∨ (p2 ∨ (p4 ∧ True))) → (((p1 ∨ (((((p3 → p3) ∧ ((p1 ∨ True) ∧ p5)) → False) ∧ p5) ∧ p1)) ∨ p4) ∨ ((True → p4) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46263948073541070238326590903 : ((((True ∧ ((((((p1 ∨ True) → False) ∨ False) → p5) ∨ (p4 → p3)) → (p5 ∨ (p4 ∨ (p5 ∧ p5))))) → (p4 ∨ p3)) ∧ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785344312365084296414458705732 : (((p4 ∨ (((((p3 → ((p5 ∨ ((p5 ∨ (True ∧ (p2 → p3))) ∨ p2)) ∧ False)) ∨ p5) ∧ ((p5 ∨ p2) ∧ (p3 ∧ True))) ∨ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42676101905475857647021354385 : (((p4 ∨ (False ∨ (False ∧ ((p2 ∧ p1) → ((((True ∧ p5) → p2) ∧ (((p1 ∧ p3) → False) → p5)) ∨ (p5 ∧ (p2 ∧ p1))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112129308455709296031432550683 : (((False ∧ (((p3 ∧ p5) ∨ (((((p1 → p5) → p1) ∧ (p1 ∨ False)) ∨ ((p4 ∧ p3) → p5)) ∨ (p4 → p4))) ∧ p4)) ∨ True) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64887682130539473738867967248 : ((p2 ∨ ((p3 ∨ (p5 → ((((False ∨ p2) ∨ (p4 ∧ (p5 → p3))) ∧ p2) ∧ ((p1 → (False → p3)) ∧ p1)))) ∧ (p5 ∨ (p4 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37584441461681561677659518439 : ((((p2 → (((p4 ∨ False) → (p3 ∨ False)) → (True ∧ (((((True ∧ True) → False) ∧ p3) ∧ ((p5 ∧ p5) ∧ True)) ∨ p3)))) ∨ p2) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157788818306919235466010582713 : ((((p5 ∧ (p2 → p5)) ∧ ((p1 → (p5 ∧ (p3 ∧ p2))) → p1)) ∨ ((p2 → (p1 ∨ p5)) ∨ p5)) ∨ (((p5 → p5) ∧ p2) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66641573989975854583900159157 : ((True → (((False ∧ ((p5 ∧ (p1 → ((False ∨ False) ∨ p4))) ∧ p3)) ∨ p1) → (((p2 → p3) → p2) ∨ ((p3 ∧ p2) ∨ (p3 → p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134006566624690230186193067061 : ((((p3 ∧ ((p3 ∨ (((p5 → (p1 ∨ p4)) ∧ p2) ∧ (((p3 → p1) ∨ p3) ∧ p5))) ∧ (p5 ∨ p2))) ∧ p4) ∨ True) ∨ (p1 ∧ (p2 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150003695430657504316091661795 : ((p5 ∨ ((((((p4 ∨ ((p2 ∨ ((p4 ∨ (True → p4)) ∧ p4)) → False)) ∧ p5) → p3) ∧ p5) ∨ p4) ∨ True)) ∨ (p2 ∧ (p3 ∧ (p2 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168391965222086609972943298863 : (((p2 → p5) ∨ (p5 ∨ (p4 ∨ (True ∨ (p3 ∧ (True ∨ (p3 ∧ ((p1 ∨ False) ∧ True)))))))) → ((p4 ∨ False) ∨ ((p3 ∧ (p3 ∨ p5)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h19 =>
              -- False on the left can always be used.
              apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301802418809268970448484191692 : (False ∨ ((p5 ∧ False) ∨ ((((p2 → (p1 ∧ (False ∧ (p3 ∧ (True → (p4 ∧ p5)))))) → p4) ∧ ((False ∧ p1) ∨ p2)) → (p4 → (p4 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84617001556165008995702724087 : (((p2 ∨ ((((p4 ∨ (p3 ∨ p2)) ∧ p4) ∧ (True ∧ p3)) ∨ ((False ∨ True) ∨ p1))) → (False ∧ ((p3 ∧ (False ∨ True)) ∨ (p2 ∨ p2)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((((p4 ∨ (p3 ∨ p2)) ∧ p4) ∧ (True ∧ p3)) ∨ ((False ∨ True) ∨ p1))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141252289916109110147689607047 : (((False ∨ (p1 → ((p3 ∧ p1) ∧ True))) → ((False ∧ ((True → p5) ∧ ((p3 ∨ (p5 → p5)) → (p4 ∨ p1)))) ∨ p4)) → ((p5 → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147991304711145870825205981292 : ((((p2 ∧ (p2 ∨ ((p5 ∨ (p1 ∨ ((((p4 ∨ False) → p2) → p5) ∧ p4))) ∨ p2))) ∨ p3) ∨ (p4 ∨ p5)) ∨ (True ∨ (True ∨ (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228748367153779987246505883443 : ((p2 ∨ (p5 → p4)) ∨ (True ∧ (((((p5 ∧ p5) ∨ (((False → p2) → p4) → p5)) ∧ False) ∨ ((p2 ∧ p5) ∨ (False ∧ p4))) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135061306863516709864309419211 : ((((((p1 ∨ False) → (p4 ∧ False)) ∨ ((((False ∧ (True → (p5 → p1))) → False) ∧ p4) ∧ p5)) → p1) ∨ (p3 → True)) ∨ (p4 ∨ (p1 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117235221101453994569415889084 : ((True ∧ (p3 ∧ (((p2 → (p4 ∧ p3)) ∨ (True → (False ∧ ((p5 ∨ True) ∨ ((p3 ∧ p5) ∧ False))))) ∧ ((p3 ∧ False) ∧ p2)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748374507626212946393820044482 : ((((p2 → p2) → (p4 ∨ (p3 → (p3 → ((((p2 ∨ (((p2 ∨ True) ∨ (p3 ∧ (p2 ∨ p5))) → p2)) ∧ (p1 ∨ True)) ∧ p3) ∨ True))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233176564225180643248130891160 : ((p5 ∧ (p2 ∨ p1)) → (((p5 → (((p4 ∨ ((p3 ∧ ((True ∧ ((True → p4) ∧ p1)) ∨ p3)) ∨ False)) ∨ p2) ∨ (p3 ∧ p2))) → p1) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → (((p4 ∨ ((p3 ∧ ((True ∧ ((True → p4) ∧ p1)) ∨ p3)) ∨ False)) ∨ p2) ∨ (p3 ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743100635828507638192768527130 : ((((p4 → p1) ∨ (True → (((((False ∧ (p3 ∧ p5)) ∨ (True ∧ p2)) → p5) → (((p1 ∧ p3) ∧ ((p3 → p3) ∨ p4)) ∧ False)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51560485643775678970183844410 : (((True ∨ (True → ((((p4 → (p5 ∧ ((p2 ∧ p5) ∧ False))) ∨ p5) → (p5 ∧ True)) → p3))) → ((p5 → ((False ∧ p1) ∧ False)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52258833476144959441494293241 : (((p3 ∨ ((((p4 ∧ ((p4 ∧ p2) ∧ p5)) ∨ True) ∧ p3) ∨ (p1 ∧ (False → p2)))) → ((((p1 ∨ False) ∨ (p1 → p2)) → p5) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655194721028174749701873350477 : ((((((p3 ∨ (((p5 → p4) ∧ ((p1 ∨ p5) → (False → (p2 ∧ False)))) → (p4 ∧ (True ∧ True)))) ∧ p2) ∧ (p2 ∧ p2)) ∨ (p3 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_689988863179303835033257371077 : ((((p1 ∧ ((p3 ∧ p2) ∧ ((p2 ∧ p5) → (((p2 → p4) ∧ (p1 ∨ p1)) → p4)))) ∨ ((((False ∧ p3) → p3) → (p4 ∧ True)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_715274688028264432710273751112 : ((((p2 → (True ∨ (p2 ∧ (p5 → True)))) → ((p4 → (p1 ∨ ((p4 ∧ ((((p3 ∧ p4) ∧ True) ∧ False) ∧ (p2 ∧ p4))) ∨ p3))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_590945671145854200613285446528 : (((((p1 → (((((p2 ∨ ((p3 → ((p2 ∨ p1) → True)) ∧ (p5 ∧ (True → p1)))) ∧ p3) → True) ∧ (p3 ∧ p3)) ∨ p1)) → p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60221879747908444110203401708 : (((True → p2) → ((((p5 → (p4 ∨ False)) ∧ (p4 ∨ (True ∧ ((False ∨ (p5 → ((p1 ∨ p4) → p4))) → (p4 ∨ True))))) ∧ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166243823895991270138097292869 : ((p3 ∧ (((((p4 → (p5 → ((True → p5) ∨ True))) → (p5 ∧ p2)) ∧ False) ∨ p4) ∧ p1)) ∨ (((p1 → True) ∨ (p1 ∧ (False ∧ p5))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349753673272273488530487608615 : (p4 → ((((p2 ∨ p2) ∨ (p5 → p4)) ∧ ((((((True ∧ p3) → True) ∨ True) → p5) ∨ (p2 ∨ True)) ∨ (p4 ∧ ((p5 ∧ p2) → p3)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_354886038552752248700131106861 : (p5 → ((p2 ∧ (p4 ∧ (((False ∧ False) → (p5 ∨ p5)) ∧ (((p1 → ((p5 ∨ p2) ∧ p5)) → ((False ∧ p1) → (p4 ∧ p4))) → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116193869719609190868229858995 : ((((p5 ∧ p1) ∧ True) ∨ (((p2 ∨ (p2 → (True ∨ (p3 ∨ ((p4 ∧ (p1 ∨ p4)) ∨ p5))))) ∨ p3) ∧ (False ∧ (False → p5)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624050110308531750307668293173 : ((((p2 ∨ ((((p1 ∨ True) ∧ (p2 ∨ True)) ∧ (p3 ∨ (p2 ∧ p4))) ∧ (p5 ∧ (p2 ∨ (((p3 → p1) ∧ p5) → (p2 → False)))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_787949316824952037292278808143 : (((p4 ∨ (p4 → ((p4 → (((True ∨ p5) → ((False ∨ p4) → p5)) → False)) ∨ ((False → (p2 → ((False → False) → (p5 → p3)))) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42747022970497141654113950937 : (((True → ((p5 ∨ (p3 → True)) → ((p3 ∧ p3) ∧ (((((((p5 → p1) ∨ p3) ∨ p4) → p4) → False) → p4) ∧ (p3 ∨ p4))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110960950170160827979011274047 : (((((p4 ∧ ((p1 → (True ∨ p2)) ∨ p3)) → (p3 ∧ (True → ((p4 ∧ p1) ∧ (True ∧ (False ∧ False)))))) ∨ (p4 → p5)) ∧ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165399123980316389324206610339 : (((True → ((p4 ∨ p3) ∨ ((p1 ∨ ((p3 ∧ True) ∨ p1)) → p4))) ∨ (True ∨ (p5 ∨ p4))) ∨ (((True ∧ p4) → (p1 → p2)) ∨ (p4 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207402832592141863069596409202 : (((p3 ∧ (p3 → (p1 → p1))) ∨ p2) → ((((p2 ∧ (p2 ∨ p4)) ∧ ((p3 ∨ p3) ∨ False)) ∨ (((p3 ∧ False) ∧ False) → (p1 → p5))) ∨ p2)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315349856175380787719060644453 : (p3 ∨ (((True → p2) → True) ∧ (p1 ∨ (((((False → p1) → ((p2 ∨ True) → p1)) ∧ (p5 ∧ (p2 → p2))) ∧ (p2 ∧ (p4 ∨ False))) → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h12
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66390909669817779347501416146 : ((p5 ∨ (p5 ∨ (p3 ∧ ((p3 ∧ p5) ∧ (((True → p5) ∧ p3) ∧ (((False ∨ p3) → (p3 ∨ True)) → ((p3 → False) → (p3 ∨ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197263317259413916705395838104 : (((((p1 → p5) ∧ p5) ∧ (p3 ∨ True)) → p4) ∨ ((p2 ∨ True) ∨ (True ∨ ((((p3 ∨ p1) ∨ ((True → p1) ∨ True)) ∨ p4) ∧ (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65806419790658102520058532660 : ((p4 ∨ (((((p5 ∨ (p4 ∧ p2)) ∧ False) ∨ True) ∨ p1) ∨ (((True ∧ p3) → p2) → (((p2 ∨ ((p5 → p1) ∨ p1)) ∧ p3) ∨ False)))) ∨ p4) := by
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
theorem thm_5_vars_173336640072053695934157128808 : ((p2 → (p1 ∧ (((p5 ∨ p5) ∧ False) ∨ ((p2 ∧ (False ∨ (p2 → p5))) ∨ True)))) ∨ (((True ∨ ((p2 ∧ p5) ∧ p5)) → p1) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112229622513925264367937771207 : (((p2 ∨ ((p1 ∧ ((p1 ∧ (p5 → ((p1 ∨ ((p2 ∧ p4) ∨ (p3 ∧ False))) ∨ (False ∨ p1)))) → (p3 ∧ p2))) ∨ p4)) ∨ p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140451006754296788487383573055 : ((((p4 → True) ∨ (p2 → (p5 ∨ (p3 → ((False ∧ (((p3 ∨ p4) ∨ p4) ∨ False)) ∧ p5))))) → (p4 ∧ (True ∧ p2))) → ((p1 ∨ p2) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → True) ∨ (p2 → (p5 ∨ (p3 → ((False ∧ (((p3 ∨ p4) ∨ p4) ∨ False)) ∧ p5))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((p4 → True) ∨ (p2 → (p5 ∨ (p3 → ((False ∧ (((p3 ∨ p4) ∨ p4) ∨ False)) ∧ p5))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308536484037357779615318015956 : (p2 ∨ (((True → ((p4 ∨ p4) → ((p5 ∨ (p1 → (p1 ∧ True))) ∧ p1))) ∨ (((((p3 → p3) ∨ False) → True) ∨ True) ∧ (p4 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149175960225898555391187057706 : (((True → p3) ∧ (((p1 ∧ (((True → (p2 ∨ p1)) → ((p5 → True) ∨ p4)) ∧ (p2 ∧ p1))) ∨ p1) ∧ p5)) ∨ ((p5 ∧ False) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245598422870492558149576631998 : ((p3 ∧ False) ∨ (((p2 → (p5 → (p1 ∧ (p5 → ((p3 → p5) ∧ ((((p2 ∨ p5) ∧ p2) → False) → (False ∨ p2))))))) ∧ p2) → (p1 → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313174273089680833108343631769 : (p3 ∨ (((p5 ∧ (p4 ∧ (p4 ∧ (False → (p1 ∨ p2))))) ∧ (((p2 ∧ ((True ∧ p5) ∧ (True → False))) ∧ (p1 ∨ (p4 → p2))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165350635857684622329854850519 : (((True ∧ ((p3 ∨ (((p5 → p4) ∧ p4) ∧ p2)) ∧ (True → p3))) ∧ (True ∨ (p4 ∨ False))) ∨ ((p1 → p3) ∨ ((p2 → (p2 ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110615918351938356498242760706 : ((p5 → (((p1 ∧ p4) ∧ ((((p5 → (False → (p5 ∨ True))) → (p4 ∧ (p2 ∧ False))) ∨ p4) ∨ (False ∧ True))) ∨ (True ∨ p1))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185086488970680583383159376437 : (((p2 ∨ p5) ∨ ((p3 → ((p2 ∨ p1) ∧ (False ∨ True))) ∧ p1)) ∨ (p5 → (((p5 ∨ (p1 → p4)) ∨ p4) ∧ (((False ∧ p3) → p4) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695798964943508387345416838855 : ((((((False ∧ False) ∨ p1) → ((True ∨ True) → ((p5 ∧ (p2 ∧ p4)) → p1))) → (p3 ∧ (((p4 → ((p2 → True) ∧ True)) ∨ True) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_462508769364891734333296272034 : (((((((p3 ∨ p3) ∧ ((p4 ∨ False) ∧ p1)) ∨ ((p5 ∨ (True ∨ True)) ∨ p5)) ∨ True) ∨ (((p3 → (p4 ∨ (True ∨ p3))) ∧ p4) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345520747641811064174834789452 : (p3 → (((p4 ∨ (((True ∨ True) → (False ∨ (p1 → (p2 ∨ p3)))) ∧ p1)) ∨ (((((False ∨ (False ∧ p4)) → True) ∧ p4) ∨ True) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_46839095194888142403900017935 : ((((((False ∧ (p4 ∨ ((True ∧ p3) → p1))) ∧ p3) ∨ (((p3 ∧ p5) ∨ p1) ∧ (((p3 → False) ∨ p2) ∨ p3))) ∧ p1) ∨ (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355206190142979350540040391307 : (p5 → ((((p2 → False) ∧ ((p3 ∨ (True → True)) → False)) ∧ ((((p2 ∨ True) ∨ p2) ∨ False) ∧ ((True ∨ (p5 → p1)) → (p4 → p1)))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : (p3 ∨ (True → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h20 := h5 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680841278136762742603245521390 : (((((p4 → (p3 ∨ p5)) ∨ (((p5 ∧ True) ∨ p5) → ((((p2 ∨ True) ∧ True) ∧ (True → p3)) ∨ p5))) → (p4 ∧ ((p1 ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39970353946641016228780544360 : (((p4 → ((p1 ∧ True) → ((((True ∧ ((p2 ∧ p5) ∧ ((True → p5) ∨ False))) → (p1 ∨ ((False → False) → p2))) → False) ∧ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135586807936554362111888782275 : ((((True → (((p3 → False) ∨ (False → ((p3 ∨ True) ∧ p5))) → False)) ∧ (p4 → p4)) ∨ ((p4 ∧ (p4 ∧ p4)) → p4)) ∨ ((p2 ∧ p1) ∧ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112640238987812266557313686431 : ((((False ∧ (True → (p1 ∨ (((p4 ∨ p4) ∨ (p3 → ((p3 ∨ ((p1 ∨ p4) ∨ p2)) → p5))) → True)))) → (p1 ∧ True)) → p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54592418866977445246022507510 : (((p5 ∨ (p3 ∨ ((False ∨ False) ∧ (p2 → p5)))) ∨ (((False ∨ p4) ∨ True) ∨ (((True ∨ (p4 → p4)) ∨ (False → (True ∨ p4))) → p4))) ∨ p1) := by
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
theorem thm_5_vars_119052416226733410953463357664 : ((p1 → ((p4 ∧ ((((True → (((p4 ∧ (False ∨ p1)) ∧ p3) ∨ p4)) ∧ p2) ∨ False) ∨ (False ∧ (p4 → (p4 → p3))))) ∨ p1)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746865067849002901722748993441 : ((((p4 ∨ True) → (((((p2 ∨ True) → p5) ∨ p3) ∧ False) ∨ (p1 → ((p3 ∨ p3) ∨ (((False ∧ p2) ∧ False) ∨ ((p4 ∨ False) → p1)))))) ∨ p5) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40948135207084177104100337556 : ((((((p5 ∨ (p4 ∨ (((p5 ∧ (p2 ∨ True)) → False) → False))) ∧ ((True ∨ p3) ∨ (True → p2))) ∧ (p5 ∨ p1)) ∨ (p4 → p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254889246401183701374216151982 : ((p4 ∧ True) → (((((p3 ∨ True) → p2) → p1) ∨ (True → (p1 → ((False → (p1 ∨ ((False ∧ p2) ∧ (p1 → p3)))) → p2)))) ∨ (p4 → True))) := by
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
theorem thm_5_vars_84106277910172999966298899962 : (((((p2 ∨ True) ∨ True) → ((((p2 → (p4 ∧ p3)) → p1) ∧ (True ∨ p3)) ∧ False)) ∧ (True ∨ (((True → (p3 → p4)) ∨ True) → False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∨ True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((True → (p3 → p4)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184945870110407339026091217926 : ((((False → False) ∧ True) → ((p2 ∧ (p1 ∨ True)) ∧ (p1 ∨ p4))) ∨ ((p1 ∨ ((False ∨ (p2 ∧ ((p5 ∧ p1) → p5))) ∧ (p2 ∧ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227998187494989599667264273789 : ((p3 ∧ (p5 ∨ p1)) ∨ (p2 ∨ ((((((((p3 ∧ p1) ∨ p5) ∨ True) → p2) ∧ p3) ∧ (p5 ∧ (p5 ∧ False))) ∨ (p4 → (p2 → p2))) ∨ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197295837897211163341049616595 : ((((p2 ∨ (p5 ∧ False)) → (p1 ∧ p5)) → p5) ∨ ((p1 → (((p2 → True) ∨ True) ∨ ((((p5 ∧ True) ∧ False) ∧ p2) → p2))) ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_102704671026110818164179512971 : (((((p5 ∧ (((p3 ∨ p1) ∨ True) ∧ ((((p3 ∧ p4) ∧ False) → p4) ∧ False))) ∧ ((p5 → p2) → (p2 ∨ False))) ∨ p2) ∨ True) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164611625218671384657615573718 : (((p2 ∧ ((p1 ∨ (((p4 → (p3 → False)) ∧ True) ∨ (p2 → p4))) ∨ (p3 ∨ p1))) ∧ p4) ∨ ((True → p3) ∨ (p3 ∨ (False → (p4 ∨ p2))))) := by
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
theorem thm_5_vars_324216466287846144865548801276 : (p5 ∨ ((p5 → ((False → p4) ∧ (p2 ∧ ((False ∧ False) ∧ p4)))) → ((p2 ∧ ((p3 ∨ True) ∧ p3)) → (p5 → ((p1 ∨ p3) ∧ (p1 ∧ p2)))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- False on the left can always be used.
    apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h2.left
  let h29 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h29.left
  let h31 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h33 =>
    -- One of the premise coincides with the conclusion.
    exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157399376719743969219723229965 : ((((((p2 ∨ (p5 ∧ p3)) ∨ (p5 ∨ (p4 ∧ p5))) ∧ (True ∨ p5)) ∧ (p4 → p3)) ∧ (p2 ∨ p3)) ∨ (((p3 ∧ False) ∨ (p3 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134460402395071407478675530013 : ((((((p2 ∧ p2) → (p2 ∨ p4)) ∨ ((p4 ∨ (True → ((p4 → (p2 ∧ p1)) → p2))) ∨ (False ∨ p1))) ∧ p3) → p4) ∨ (p2 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



