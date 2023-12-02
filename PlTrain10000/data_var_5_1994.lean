variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317706174970093594928938758106 : (p4 ∨ (((((p4 → (p4 ∨ ((False ∨ (((p4 ∧ p3) ∧ ((False ∨ p4) ∧ False)) ∨ False)) ∧ p3))) ∨ True) → (p3 ∧ p3)) ∨ (False ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_59035795439653820766049086393 : (((p4 ∧ p1) ∨ ((p5 ∧ ((p5 ∧ p2) ∧ ((False → (p4 ∨ ((p3 ∨ ((p2 → p5) ∨ (False ∧ (True ∨ False)))) ∧ False))) ∨ p3))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303789385102586843275316020975 : (p1 ∨ ((((p2 ∧ (p2 ∨ ((p4 ∨ ((((True → ((p4 ∧ p4) → (p2 ∨ True))) ∧ (p2 ∨ p3)) → p5) → p4)) ∨ p2))) ∨ True) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711907368898602670499481223588 : (((((False → ((p3 ∨ p4) ∨ p5)) ∧ p3) ∨ (p4 ∧ ((((True → p3) ∨ p5) ∧ False) ∧ (p1 → (p2 ∧ ((p3 ∧ p2) ∧ (p5 ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61766747462342571668650934037 : ((p2 ∧ ((((p3 ∨ (p5 ∨ ((True ∨ (p2 → (p1 ∧ False))) ∧ ((True ∨ p1) ∨ False)))) ∨ (p4 ∧ (p3 → p3))) ∧ (p1 → False)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661322490697590018377680561822 : (((((((p3 ∧ (p5 ∧ (((p5 → ((p1 ∧ (p3 → p3)) ∧ p1)) ∨ p3) → p4))) → p2) ∨ (p5 ∧ True)) → (p5 → p4)) → (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192041089580079766350622488366 : ((p2 → (p1 ∧ ((p5 → True) → (p3 ∧ (p4 ∨ False))))) ∨ (((True → ((((False ∧ p4) ∨ p4) ∧ ((p3 → True) ∧ p3)) ∧ p4)) → p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806254948033816096516346190244 : (((p4 → (((p2 ∧ (((p5 ∨ (p1 ∨ ((p1 → p4) → (True → True)))) ∨ (False → p3)) → p2)) ∨ (((p5 ∨ False) ∨ True) → True)) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48022596463361576389817690255 : ((((p5 ∨ (p4 ∧ (((((p5 ∨ p4) → p5) ∨ False) → p3) ∨ p3))) ∨ (p1 → (p3 ∧ (p2 ∧ (p5 ∧ (p4 ∧ p1)))))) → (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44975204831483756380069976779 : ((((p1 → p1) ∧ (((True → (((p4 ∨ p1) ∨ p1) ∨ p3)) ∨ (p3 ∧ (p1 ∧ True))) ∧ (((p1 ∧ False) → p5) ∧ (False → p1)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653676330532658292732278878668 : ((((((((False ∨ (p5 ∧ p1)) ∨ (((p1 → (p3 ∨ ((p3 ∨ True) ∨ (p4 → False)))) ∨ True) ∧ p3)) → p1) → p1) ∧ p2) ∨ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120731112105581541355145121787 : ((((((((p3 ∧ (p1 ∨ ((False → (True ∨ True)) ∨ p2))) → (False → p4)) ∧ True) → p2) ∧ (False → False)) → (True → False)) ∨ False) → (p4 → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187779928137212076225625323386 : ((p3 → ((((p4 → p1) ∧ (p2 → (p1 → p4))) ∧ p3) → p1)) → (((p2 ∨ (p2 ∧ True)) ∨ p2) ∨ (p1 ∨ (True ∧ (p3 → (p3 ∨ p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789018486779243108037108494028 : (((p5 ∨ ((((((((((True ∨ (True → p3)) ∧ True) ∧ p4) → False) ∨ p3) ∧ p4) → p4) ∨ p3) ∨ (p5 ∨ (p2 ∨ p1))) → (p3 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37668075730693964165338685691 : (((((p2 ∧ (((True → (((p4 ∨ p2) ∨ p2) → p1)) ∨ p4) ∧ (p4 → ((p2 ∧ (p5 → False)) ∨ (p1 ∨ p4))))) → True) → p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136689207111052331864200183681 : (((True ∧ True) ∧ (p4 ∨ (p2 ∨ (p1 ∨ (p5 ∨ ((p3 → p3) ∧ (p3 ∨ ((False → False) → (p2 → (True ∧ True)))))))))) ∨ ((p3 ∨ False) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165155234423242417964594340225 : ((((True ∧ (p3 → ((True ∨ p3) ∧ p1))) → (p4 ∨ (p4 ∧ (p5 → p2)))) ∧ (p5 → False)) ∨ ((True ∧ ((p1 → True) ∧ (p4 ∧ False))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261521621149964870416748666976 : ((p5 → p3) → ((((p2 ∧ p2) ∧ ((p4 → p4) ∧ p1)) ∨ p4) ∨ (((p2 → (p1 ∧ (p5 ∨ True))) ∧ (True ∨ ((False ∨ p5) ∧ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214732482546639410906870770770 : (((p3 ∧ True) ∨ (False ∨ p1)) ∨ ((((False → False) → (p1 ∨ p1)) ∨ ((p2 → False) ∨ p2)) ∨ ((p3 ∧ p1) → (((p1 → p3) ∨ p3) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312069508532796688431525168210 : (p2 ∨ (p5 ∨ (((p2 ∨ True) ∧ ((p3 ∧ ((p4 ∧ True) ∧ (p3 → p4))) ∨ p5)) → (((p5 ∧ (False ∧ p5)) ∧ p3) ∨ (p5 → (False → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158045865448312077915038907659 : (((((p4 ∧ p4) → True) ∧ (p2 → p3)) ∨ ((p1 ∨ ((p4 ∧ p2) ∨ (False ∨ p3))) ∧ (True ∨ True))) ∨ ((p2 ∨ (False ∧ (p1 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196502843009923514337414909685 : ((p2 → ((p2 ∧ (p4 ∧ (p4 ∧ p2))) ∨ p2)) ∧ ((p1 ∧ p1) → ((True ∨ p2) → ((p2 ∧ ((p4 ∨ p2) → False)) → (p3 → (False ∨ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : (p4 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54772002516340971685850420748 : (((True ∧ ((False → p5) → (p3 ∧ (False ∨ p5)))) → ((p1 → ((p1 ∧ p5) ∧ ((p2 ∧ (p4 ∧ (p3 ∧ (p4 ∨ False)))) ∧ p1))) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330890160186386509954972902473 : (True → (p3 → (p5 ∨ (p4 ∨ ((p2 ∧ (p4 ∨ ((((True → p5) ∨ (p4 ∧ (((False ∨ p5) → p4) ∧ (p1 → p3)))) → p2) ∨ p3))) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48968338799532943610462470867 : (((((((p1 ∧ (p5 → (p2 → (p4 ∨ ((p2 ∨ (False → p4)) → p1))))) → (p3 ∨ p4)) ∨ True) → False) ∨ True) ∨ ((p3 ∧ p1) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118650421363169272793405369165 : ((p4 ∨ (p2 ∧ (((p2 ∧ (((False ∨ (p4 → p1)) ∧ ((False ∧ (True ∨ True)) ∧ ((p1 ∨ p3) ∧ True))) ∧ True)) → p5) → False))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302731426737301578024652292678 : (False ∨ (p3 ∨ (p4 → ((p2 ∨ p2) ∨ (False ∨ (True → ((False → ((p5 → p5) → ((p1 ∧ p4) ∧ (p3 ∨ p2)))) ∧ ((True ∧ True) ∨ False)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348172042364331104544377142558 : (p3 → ((p1 ∨ p5) → ((False ∧ (p4 ∨ p3)) ∨ ((p4 ∧ (p1 ∨ ((p5 ∨ False) → (((p4 ∨ (p5 → (p5 ∨ True))) → False) ∧ True)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186801547306038353373390068017 : ((((p2 ∧ p5) → (p2 ∨ False)) ∧ (p3 ∨ (True ∨ (p1 ∨ False)))) → ((p2 → (True ∧ p3)) ∨ (True ∨ (p2 ∧ ((p5 → (p1 → False)) ∨ p3))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173467827901090937575319634047 : (((((False ∧ (False ∧ True)) → ((True ∨ (True ∨ False)) ∨ (False ∧ p1))) ∨ False) ∧ p5) → (((p1 ∨ p4) ∧ (p3 ∧ p2)) ∨ ((p1 ∨ p5) ∨ False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180275121696226527309588765763 : (((p2 → (((p1 → (p3 → (p2 ∧ True))) ∨ (False ∧ p3)) ∨ p3)) → False) → (((p5 ∨ ((False ∧ False) ∧ (p3 ∨ False))) ∧ p4) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318556806738072625828006931922 : (p4 ∨ ((((((p1 ∧ (True ∧ (p2 ∨ (p1 ∨ ((p1 ∨ (p5 → True)) ∨ p5))))) → True) ∧ p4) ∨ ((False ∧ p1) ∨ p3)) ∨ True) ∨ (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330401566793757966153195004361 : (True → (p2 ∨ (p2 ∨ (((False → (False ∧ p4)) → (((p3 ∧ p2) → (p5 ∨ (p1 ∧ True))) → False)) ∨ ((p3 ∧ p5) → (True ∨ (p3 ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309800798118257428960812832102 : (p2 ∨ (((True → ((p4 ∨ (p2 ∨ p3)) ∨ (False ∨ p4))) → (p1 → ((p1 ∧ p2) ∨ (p5 → (p2 ∧ p3))))) ∨ (p3 → (p5 → (True ∧ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136294912866713653665256912935 : (((p3 ∨ (p3 ∨ (p3 → (p4 ∧ p3)))) → ((((p4 → p2) ∧ (p2 ∧ p3)) ∧ (False ∨ (True ∧ True))) ∨ (p1 → True))) ∨ ((p1 ∧ p3) ∨ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53198359997724349577020183635 : ((((True ∧ ((((p3 → p5) → False) ∨ p1) ∨ p5)) ∨ (p3 → False)) ∨ (p4 → (p1 ∨ ((p2 ∧ p3) → (p4 ∨ ((p1 ∧ True) → False)))))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135760993323359879982582097678 : (((p3 ∨ (p1 → (p2 ∨ ((p3 → (p3 → p2)) ∧ ((False ∧ p1) ∨ p1))))) ∨ (False ∨ (((p3 → p3) ∧ True) ∧ True))) ∨ (p5 ∧ (p1 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75671220917963549203382216988 : (((((((((False ∨ False) ∧ False) ∧ (p1 → (((p3 ∨ p2) → p2) ∧ p5))) → True) → (p5 ∨ (p3 ∨ (p2 → p4)))) ∨ False) ∨ True) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((False ∨ False) ∧ False) ∧ (p1 → (((p3 ∨ p2) → p2) ∧ p5))) → True) → (p5 ∨ (p3 ∨ (p2 → p4)))) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121545856353015129616432777680 : ((((p1 ∧ (((((False ∧ (p4 → p3)) → p5) ∨ True) ∨ (p3 → p2)) ∨ ((False → (False ∧ False)) ∨ p4))) ∨ (p4 → p1)) → False) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157631772631367876030368299463 : ((((p2 → True) ∧ ((((p2 ∧ p3) ∨ (p5 ∧ (True ∧ p4))) ∨ p5) ∧ p4)) ∧ ((p3 ∧ p5) ∧ p1)) ∨ ((True ∧ ((p2 → p3) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191534717089647697139865279451 : ((p1 ∧ ((p4 → ((p5 ∨ (p4 ∨ True)) → p5)) ∧ p2)) ∨ (((p4 ∧ ((True → True) ∨ p5)) ∨ ((p4 ∨ (p1 → p2)) → False)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166146229913665055773689890328 : ((False ∧ (((((False ∧ p2) ∧ ((p4 ∨ p1) → (False → p2))) ∨ (p2 ∨ p4)) ∧ p5) ∧ p3)) ∨ (((p2 ∧ p5) ∧ (True ∨ False)) → (False ∨ p2))) := by
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
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39943531569453695515055303979 : (((p4 → ((((p2 ∨ p2) ∨ (((p3 ∧ (False ∧ (True → ((True → (p5 → (p4 ∨ p2))) ∨ p1)))) ∨ p4) ∨ p1)) ∨ p2) ∧ True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613828053274475873679805905295 : ((((((((((p3 ∨ (True ∨ (p2 ∨ p1))) → p5) ∨ p1) ∨ ((True → (p5 → False)) ∧ p3)) ∧ p4) ∧ True) ∨ ((p4 → False) → True)) ∨ p5) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118228708328070280985268409645 : ((p1 ∨ (((((p5 ∨ (p2 ∧ p3)) ∧ p4) ∨ ((p1 ∨ ((p3 ∨ True) → p1)) ∧ (True ∨ ((p2 → p3) ∨ p4)))) ∧ True) → p4)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185248618260672392930994341257 : ((p1 ∧ ((p3 → (p2 ∧ (p4 → ((p3 ∧ p2) → False)))) ∧ True)) ∨ (True → (p4 ∨ (((p1 ∧ False) ∨ False) ∨ (((p3 ∨ p4) ∧ p1) ∨ True))))) := by
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
theorem thm_5_vars_337670175983796945314535277329 : (p1 → (((p3 → True) ∧ ((True ∨ p4) → ((p2 ∨ ((p2 ∨ True) → (p5 → (p5 → p1)))) → False))) ∨ ((p2 → p2) ∧ (p1 → (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63260269172114945467698770770 : ((p5 ∧ (((p1 ∨ (p2 ∧ p1)) → ((False ∨ p1) → p2)) → ((((p5 ∨ (p4 ∨ True)) ∨ ((p3 ∨ p2) ∨ p1)) → (p3 ∨ p1)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336209414939120564991225758859 : (p1 → ((((((p2 ∧ (p3 ∧ (True ∨ (p4 ∧ (((p1 ∨ p2) ∧ p3) → False))))) ∧ False) ∧ (True → False)) → (p5 ∨ p4)) → (p2 ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8187176310322032938464910248 : ((((True → (((False ∨ ((p4 → p4) → p4)) → ((p5 → (p2 ∧ p2)) ∨ (p4 → (False → p4)))) → ((p2 ∨ p4) ∨ True))) ∨ p1) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_351387885452265056138714501973 : (p4 → (((False ∨ ((((p1 ∨ p5) ∧ p2) → (p4 → (p1 ∨ (p5 ∧ (p5 ∧ True))))) → (False ∨ p2))) ∧ p5) ∨ (((True ∨ p4) ∨ p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212226367316707539100817359113 : ((False ∨ ((True → True) ∨ p1)) ∧ (((p4 → (p5 ∧ p4)) ∨ (p4 ∨ (((p4 ∧ (p3 → p5)) ∨ (p5 ∧ ((p1 ∨ p1) ∨ p3))) → p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4986855024154190429535801039 : ((((((((((True ∧ p5) ∧ (p3 ∧ False)) ∧ (p2 ∧ (p5 → p2))) ∨ False) ∧ (p1 ∧ (p2 ∨ (p2 ∧ False)))) ∧ p5) ∨ p3) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232056595467916149427488788439 : (((p4 ∨ True) → False) → (((p4 ∨ (p1 → (((False → p2) ∧ (p5 → p5)) ∨ (((p4 ∧ (p1 ∧ p3)) ∧ p1) ∧ (p1 ∨ p4))))) ∧ p5) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54506452397538062283739093448 : ((((p2 ∨ (p2 ∨ p4)) ∨ (p5 ∨ (p1 → p4))) ∨ ((False → p5) → ((False → ((p1 → False) ∧ (p3 ∨ p3))) ∨ (p2 ∨ (p4 ∧ False))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256804390202865940536168703192 : ((p1 ∨ p2) → (p1 ∨ (p3 → ((((p2 → p4) → p5) → (False ∨ ((True ∨ p5) ∨ ((p4 → p4) ∨ True)))) → ((p5 ∨ (True ∧ p4)) ∨ p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54517938897822099170199459565 : ((((p4 ∧ p4) ∧ (((p5 ∧ p3) → p4) → p5)) ∨ (((p4 ∧ ((p1 → p5) ∨ p1)) ∨ (((p4 → p3) ∨ p5) ∨ True)) ∧ (p4 → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303754363626351419132742305825 : (p1 ∨ ((((p2 → ((True ∨ ((p2 → (((p3 ∨ False) ∨ False) ∧ ((p1 ∨ (True → p2)) ∨ True))) ∨ p4)) ∨ (p3 ∧ p3))) → False) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777516553578391638575875774470 : (((p1 ∨ (((((p3 ∨ True) ∧ ((p2 ∨ p3) → False)) ∧ p3) ∧ (True ∧ (p1 → p3))) → ((p3 → p5) ∧ ((p3 ∧ (p3 ∧ False)) ∨ False)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h17 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h18 := h8 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h20.left
    let h27 := h20.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h28 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h29 := h24 h28
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h20.left
    let h32 := h20.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h33 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h34 := h24 h33
    -- False on the left can always be used.
    apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112337283217734565540107486129 : (((p4 → (p1 → (((p5 ∧ ((p5 ∨ False) ∧ (p1 → (p5 ∨ (p4 ∧ (p3 → ((False ∨ p2) ∨ p4))))))) ∨ p1) ∧ True))) ∨ p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114255859802557269507843649680 : (((p2 → (((((p5 ∨ (p3 ∧ p1)) → p4) ∧ True) → ((p5 → (p1 → p5)) ∧ p5)) ∧ (True ∨ False))) → (p1 ∧ (p3 → True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197092047938258990360884774763 : (((p2 ∧ (False → ((p4 ∧ p5) ∧ False))) ∨ False) ∨ ((((((True ∨ p3) ∧ (False → False)) ∨ False) → ((p4 ∧ p5) ∨ (p1 → True))) ∨ p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56093446077655234982324208135 : ((((p4 ∧ True) ∧ (p1 ∧ p4)) ∨ ((p4 ∧ (True ∧ p2)) ∨ ((((p3 ∨ ((p2 ∧ p4) → False)) ∨ p1) ∧ (p4 → (p3 ∨ p4))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43336007038081868802019141737 : ((((((p1 ∧ ((True ∨ ((p4 ∧ p2) ∨ p4)) ∨ (True ∨ (False → p5)))) ∧ ((p1 ∨ True) → ((p1 ∧ p2) ∧ p2))) → p4) ∨ p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254149037414252233971595086734 : ((p2 ∧ p1) → (((True → (True ∨ ((p4 ∧ (p3 ∨ ((p2 → True) ∨ (False ∧ (p5 → p5))))) ∨ (p4 ∧ True)))) → ((p2 ∧ p4) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317802705938394188136288970407 : (p4 ∨ (((((p4 ∨ False) → p5) ∧ (p3 ∨ (p5 ∨ p1))) → ((((False ∨ (p5 ∧ (p2 ∧ p2))) ∨ True) ∨ (p2 ∧ True)) ∨ (True ∨ p3))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
theorem thm_5_vars_634106950082039174666458725983 : ((((((((p1 → p1) → (p4 ∨ False)) ∧ p4) → ((((p3 ∨ (p2 ∨ (p5 ∧ p4))) ∧ p2) ∨ (False ∨ p5)) ∧ False)) → (True ∧ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43592659274886198309565712039 : ((((((p5 → p5) → ((((p4 → p2) ∨ True) ∧ (p1 ∨ True)) ∧ ((p2 ∨ p5) ∨ (p1 ∨ ((False ∧ True) → False))))) ∨ p3) → p2) → p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p5) → ((((p4 → p2) ∨ True) ∧ (p1 ∨ True)) ∧ ((p2 ∨ p5) ∨ (p1 ∨ ((False ∧ True) → False))))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186503589154395655202677330534 : (((p4 ∨ ((p2 ∨ p1) ∨ ((p3 → p5) ∨ p5))) ∧ (True ∧ p1)) → ((((p4 ∨ (False ∨ p1)) ∧ (True ∧ True)) ∨ (p3 → p5)) ∨ (p5 ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h3.left
        let h11 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h3.left
        let h18 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h3.left
        let h21 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657700813999812486844657722936 : (((((p2 → False) → (p4 ∧ ((True ∨ ((p3 ∧ p1) ∧ p3)) ∧ (((((p1 ∧ p5) ∨ p1) ∨ True) ∧ p5) ∨ (p3 ∨ p1))))) ∨ (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739359600890362334985040945244 : ((((p4 ∧ p4) ∨ (p2 ∨ (p4 → (((((True ∨ (p3 → p1)) → (True → True)) ∧ p3) ∧ (p5 → ((p5 → p2) → p3))) ∨ (p3 → True))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147505270572747384831706090464 : (((p1 ∨ (p1 ∨ ((((((p1 ∨ p3) → p4) ∨ (p5 ∨ False)) → (p3 → (p3 → p5))) ∨ True) ∧ False))) ∨ True) ∨ ((p5 ∧ p2) → (True → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69220653068968211848731521140 : ((p5 → ((((p1 → True) ∧ (p3 → p2)) ∧ p4) → (((((True → ((p5 ∧ (p4 → p3)) → p5)) → False) ∨ p3) → False) ∨ (p1 → p5)))) ∨ p4) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754287436586974204889007636239 : (((False ∧ ((p4 → False) ∧ ((False ∨ (p5 ∨ (((True ∨ p5) → (False ∧ p1)) ∧ (p3 ∧ p4)))) ∨ (p5 → (False → ((p3 ∧ p2) ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45791100485347741965413463666 : (((p1 → ((p5 → (((((False → p2) → p1) → (False ∧ (p1 → p3))) ∧ p2) ∧ ((p2 ∨ True) ∨ True))) ∧ (p3 → (p5 ∧ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41385399021412353647089398538 : ((((((p4 → (p1 ∧ True)) ∧ ((((False ∧ p4) → p1) → p3) ∨ p2)) → p1) ∧ (((False ∧ p3) ∧ p2) ∧ (p4 ∨ (True ∧ p2)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164536858979644633870650421983 : (((((p4 ∧ (((p3 → p4) ∨ (p5 ∧ False)) ∧ True)) → p3) → (p2 → (p4 ∧ p2))) ∧ True) ∨ (False → ((True ∨ (p4 ∧ True)) → (p4 ∨ p4)))) := by
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
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638855955679238750358293263883 : ((((((p3 → (True ∨ p3)) ∨ False) ∧ ((p2 → p5) → ((False ∧ p3) ∨ (((p4 ∧ (False ∧ p5)) ∧ p5) ∨ (True ∨ (p3 ∧ False)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764314876415277949247154272072 : (((p4 ∧ ((((((p2 ∨ p1) ∧ True) → (p5 ∧ ((p5 → False) → False))) → ((p2 → p5) ∨ p1)) ∧ (p5 ∧ ((p5 ∨ p3) → p2))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337078861486806473589565325590 : (p1 → ((((((p4 ∨ p5) → False) → ((p2 → p2) ∨ p3)) → ((((p2 → p4) → p3) ∨ p3) ∨ p5)) ∨ ((p4 → p4) → p5)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307748165279552034194460558642 : (p1 ∨ (p3 → (((p1 ∨ (p1 ∨ (((p5 ∨ p5) ∨ ((p4 ∧ p3) → p2)) → p5))) ∨ p4) ∨ ((p1 → (p1 ∨ p1)) ∨ ((True ∨ p4) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674701775933857160440678021260 : ((((p2 → ((True ∨ (((p4 → False) ∧ (False ∧ (p1 → p4))) ∨ True)) → (p3 ∧ ((True ∧ p2) → (p1 ∧ p2))))) → ((p3 ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56348951308239558289852020615 : (((((p3 → p1) → p1) ∨ p4) → ((((p4 ∧ ((((p1 → (p5 → p2)) → p5) ∨ False) ∧ True)) → ((p5 → False) → False)) ∨ False) ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (p1 → (p5 → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h15 := h9 h10
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h27 : (p1 → (p5 → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h30 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h31 := h21 h30
        -- False on the left can always be used.
        apply False.elim h31
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h32 := h26 h27
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h33 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h34 := h21 h33
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- False on the left can always be used.
      apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352696854069100512475212106895 : (p4 → ((p5 ∨ p2) ∨ ((p3 ∨ ((p3 ∧ ((False ∨ p4) ∧ (p5 ∨ (p4 ∧ ((p1 ∨ (p1 ∧ p1)) → p5))))) ∧ (p5 ∨ p4))) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185805549885245414989911641875 : ((p5 → ((p2 ∨ p2) → (p2 → (((p4 ∨ p3) ∨ p4) ∨ p4)))) ∨ (((p3 ∧ ((p4 ∧ True) ∨ p5)) → (((p1 ∧ p2) → p2) ∧ p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147515072928244325932579057197 : (((p4 ∨ ((((p3 ∨ ((p4 ∧ p1) → p1)) → (True → (False ∧ p4))) ∧ ((True ∨ p3) ∨ p3)) ∧ True)) ∨ False) ∨ (((p2 ∨ p1) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800194912069199437041046752936 : (((p2 → (((((True ∨ (((((p1 ∧ (p2 → False)) → p4) → (p2 ∧ p4)) ∧ p4) ∧ (p2 → p5))) → False) ∨ (p5 ∧ p1)) ∧ p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316766358534062126330285088675 : (p3 ∨ (True → ((p5 ∨ True) → (p2 → (((p1 → True) ∨ True) → ((p5 ∧ (False ∨ p2)) ∨ ((p2 ∨ False) ∨ (False ∧ (True ∨ (True → True)))))))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118243982818496250449640702369 : ((p1 ∨ ((((True ∧ p5) ∨ (p3 ∧ p1)) ∧ (p1 → (((((p5 ∨ p4) → p5) → (p5 → p4)) ∨ p2) ∨ p4))) ∨ (p3 → False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342706146284511490629338415594 : (p2 → ((False → (((p3 ∨ p3) ∧ ((p2 → True) → p2)) ∧ p1)) → (((p5 ∨ (p3 ∧ ((p1 ∧ p2) → p4))) ∨ (True ∧ (p3 → p2))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185194526703415791920438098085 : ((True ∧ ((p1 ∨ (p3 ∨ (((p5 → p4) ∨ p4) ∨ p4))) → p3)) ∨ ((p2 → p2) → ((p1 ∨ ((p1 ∨ (p4 ∧ p2)) → p1)) ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_118471812179232098366710782903 : ((p3 ∨ (((True → False) ∨ ((p1 ∧ ((p1 ∧ True) ∧ p5)) ∧ (p3 ∧ (True ∧ (p1 → (((False → p3) ∨ p2) ∧ False)))))) → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55873561582757178789594862881 : (((True ∨ (False ∧ (p5 ∨ False))) ∧ (p1 → (((p3 → p4) ∧ p3) ∨ ((p2 ∨ ((p2 ∨ False) ∨ ((p3 → p5) ∨ (p4 → p4)))) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258791234216020538390820589705 : ((True → False) → (((p5 ∨ (p1 → p1)) ∧ False) ∧ (((False → (((True ∧ (False ∨ (p3 → False))) → False) → False)) → False) ∨ ((False → p1) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116408822198131639715541963958 : (((False ∨ (p1 ∧ p1)) → (((p4 ∧ ((False ∧ p4) ∧ ((p2 ∨ (((p1 → (False → True)) ∧ p2) → p2)) ∧ False))) ∨ False) ∨ True)) ∨ (p4 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197411841098709169304738025737 : (((p1 → (p3 → (p1 ∨ (p3 ∨ p5)))) → p1) ∨ (True ∧ (p5 ∨ (((((p2 ∨ p4) → False) ∧ (p5 ∨ ((False ∧ p5) → p3))) → p4) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656262034572740575639742804379 : (((((((p2 ∧ (p2 ∧ False)) ∨ ((False → True) ∧ False)) ∧ (p2 ∨ False)) ∧ (p4 → (True ∨ ((True ∧ p2) → (p3 → p5))))) ∨ (True ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_256692407280449413650371801009 : ((p1 ∨ p1) → ((((p3 ∧ ((p5 ∧ p4) ∧ ((((p4 ∧ p3) ∨ (p3 ∧ (p4 → ((p4 ∧ p5) ∨ p1)))) → p4) ∧ True))) ∨ True) ∨ p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200749965433788409579037750908 : ((p3 ∧ (p2 ∨ (p3 → (False ∧ (True ∨ False))))) → ((p1 ∨ (p4 ∨ ((p5 ∧ ((p1 ∧ (p3 → False)) ∨ (p5 ∨ (False → p4)))) ∧ False))) ∨ p2)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162036335865750998452660913662 : ((p4 → ((p1 → False) ∨ (((p1 ∧ p2) ∧ p1) → (True → (((p1 ∨ p1) ∧ p4) ∧ (p1 → p5)))))) → ((p1 → p4) ∨ (p2 → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



