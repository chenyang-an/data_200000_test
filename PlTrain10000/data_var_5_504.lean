variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653632647771516558514060250370 : ((((((((p3 ∨ (((p1 ∨ (True → p4)) ∨ (True ∧ False)) ∨ (p2 ∨ p3))) → p1) ∨ ((p2 ∧ True) ∧ True)) ∨ p3) ∧ True) ∨ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919536567372598462145081590682 : (((((p1 → True) → ((((p1 → (p2 ∨ p5)) ∧ (p5 ∧ False)) ∨ p3) ∧ p4)) ∧ ((p2 ∧ (False → p4)) → (True → ((p1 ∨ True) ∨ p5)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66419884054540217896435968218 : ((p5 ∨ (p3 → (p1 → ((((((((((p3 ∧ p2) ∧ p1) ∧ p5) ∨ p4) ∧ (p1 ∧ p3)) → p3) ∨ p1) → (p2 ∧ p3)) ∧ False) ∨ True)))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172661978500280730580751791129 : (((False → p2) ∧ ((p2 ∧ (p3 → True)) ∧ (p3 ∧ (False ∨ ((p3 ∨ p3) ∨ p4))))) ∨ (p4 → ((p5 ∧ p2) → (p5 ∧ ((p2 ∧ False) ∨ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160526003677396420734849505573 : (((((p2 ∨ (True ∨ ((p3 ∨ p5) ∨ True))) ∨ (False ∨ p5)) → p3) ∨ ((p4 ∨ (p2 ∨ p2)) → p3)) → ((True → False) → ((p5 ∨ False) ∨ False))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300912033986937028726702802727 : (False ∨ (((p2 ∧ p2) ∧ (True ∧ (((p5 ∧ p1) ∨ (p4 ∧ (p5 ∧ p2))) ∧ p1))) → ((p2 ∨ p2) → (False ∨ (((p5 ∨ p3) ∨ p1) ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h22.left
    let h26 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111170032566840877948358378632 : ((((p5 → ((p3 → p1) ∧ p1)) ∧ (((p4 ∧ True) → (False → False)) → (((((False → p3) → p2) ∨ p4) → p3) → p2))) ∧ p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761030073558936719866928251106 : (((p2 ∧ (p1 → ((((((p2 ∧ False) → p2) ∧ ((p4 ∨ ((p2 ∨ p1) → (p2 ∧ p4))) ∨ (p3 → True))) ∨ (True ∧ True)) ∨ False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777333054685882572646739815572 : (((p1 ∨ ((((p5 ∧ (True ∧ False)) → (((((p5 ∨ (p1 ∧ p5)) → p1) → p1) ∧ False) ∧ p1)) → p3) ∨ ((True ∨ p2) → (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672764279992398144013364184941 : ((((((p3 → p5) ∨ ((p5 ∨ (p5 ∨ ((False ∧ p3) ∧ p1))) → ((True ∧ (True ∧ False)) ∨ p2))) → (False ∧ True)) → (p1 ∨ (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47546397969804951253016783362 : (((p5 ∨ (False ∧ (p4 ∨ ((p1 → (((False → False) → p1) → True)) ∨ (((p5 ∨ False) → ((p1 ∨ p5) ∨ p4)) → True))))) ∨ (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69224837217024218423438494071 : ((p5 → ((((p1 → p4) ∨ p4) ∨ True) ∧ ((p1 → p5) → ((p4 ∧ (False ∧ ((p1 ∧ ((p4 ∨ (True ∧ True)) ∧ p3)) → False))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217786168185620433250931301743 : (((False ∨ (p1 ∧ p3)) → p4) → ((True ∧ (False ∨ ((((p5 → p2) → p2) → p2) ∧ True))) ∨ ((p5 → p1) → ((p2 ∧ p2) → (True ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135146159084352597058913276515 : (((p5 ∨ (((p5 → p4) ∧ (((p2 ∧ p3) ∧ p5) ∨ (((p4 ∨ p4) ∧ (p2 ∧ p4)) → p4))) ∧ p3)) ∨ (False ∧ p3)) ∨ (False → (False ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113846094476715688121252418405 : (((p5 ∨ ((((p4 ∧ p1) ∧ p1) → ((p2 ∧ p2) → ((p4 ∨ p5) ∧ (False ∨ (p5 → True))))) ∨ (p1 ∨ p5))) → (p4 → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729830626046692338663930716400 : (((((False ∧ True) → True) → ((((p1 ∨ p5) → (p5 ∧ p5)) ∨ (False → (False ∨ p1))) ∧ (((True ∨ ((p3 ∧ p2) → p2)) ∨ p5) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324638408405508763144519749008 : (p5 ∨ (((p3 ∨ p1) ∧ p1) ∨ (p4 ∨ (p5 ∨ ((((p4 → (((p4 ∨ p1) ∨ (p5 → (p1 ∧ p4))) → p3)) ∧ p5) ∧ (p3 ∨ p3)) → p3))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184289913663080314103250123741 : (((((p1 ∨ p4) ∧ (p1 ∨ p2)) → (False ∧ (p5 → p5))) → False) ∨ ((False ∧ (((p5 → p1) ∨ False) → True)) ∨ ((p2 → (p4 ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229533323266548472215399413429 : ((p2 → (p5 ∨ p1)) ∨ (p4 ∨ ((((p2 ∨ p2) ∧ ((True ∧ True) → (((False ∨ p3) ∧ p2) ∧ p3))) ∨ (p3 ∧ p5)) → (p1 ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77208137975195605698278407165 : (((((p4 ∨ p2) → p5) ∨ (((p3 → False) ∧ ((p4 → (p4 ∧ p1)) ∧ ((p2 → (False ∧ p1)) ∧ (p1 → (p3 ∨ p3))))) ∨ True)) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p2) → p5) ∨ (((p3 → False) ∧ ((p4 → (p4 ∧ p1)) ∧ ((p2 → (False ∧ p1)) ∧ (p1 → (p3 ∨ p3))))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590162342002670306394310905217 : (((((((((p5 ∧ (p5 ∨ True)) ∨ p4) ∧ True) ∨ p1) → (((p1 → (p1 → ((p1 ∨ p1) → (False ∧ True)))) ∨ p5) → p2)) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50720842932391683147694568236 : ((((False ∧ False) → (((((p2 → ((p5 → (p1 ∧ p3)) ∧ p2)) ∧ (p3 ∧ p4)) → p4) → True) ∨ p2)) → (p3 → (p1 → (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305711640971189305247714239696 : (p1 ∨ (((False → (p2 ∨ True)) → (True ∨ (p4 ∨ (True ∨ p3)))) → (((p2 ∧ ((((p2 ∧ p2) ∨ p1) ∨ False) → p1)) ∨ (p1 ∨ True)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164927563509171300196425581809 : (((((p2 ∧ (p3 → (p2 ∨ (p4 ∧ True)))) ∧ ((True ∨ p4) → (p3 ∧ True))) ∨ p3) → p4) ∨ ((False ∧ p4) → (p4 → ((p3 ∨ p3) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891542440940505216404282989220 : ((((p4 → (((p4 ∨ True) ∧ ((((p1 ∧ p3) → True) ∧ ((True ∧ p4) ∧ p2)) → p1)) ∨ (False → ((False → p2) ∧ p2)))) → (False ∧ p1)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (((p4 ∨ True) ∧ ((((p1 ∧ p3) → True) ∧ ((True ∧ p4) ∧ p2)) → p1)) ∨ (False → ((False → p2) ∧ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391163972905684958243664153523 : ((((((False ∨ (p1 ∧ p5)) ∨ (True → p4)) ∨ (((False ∧ True) ∨ p4) ∨ (False ∨ ((p4 → True) ∨ (p3 → (p3 ∨ (p3 → p1))))))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356395843993266856604158130459 : (p5 → ((p2 ∨ (True ∨ (((p3 ∧ ((False ∨ p4) ∨ p3)) → (p3 → False)) → p3))) → ((p1 ∧ ((False ∨ True) ∧ (True ∧ p2))) ∨ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787077030613305165070914483060 : (((p4 ∨ ((p5 ∨ p2) ∨ (True ∧ (((p5 ∧ ((p5 → False) ∧ p2)) ∨ p3) → ((p3 ∧ ((p3 ∨ True) ∧ ((False ∨ p1) ∨ p5))) ∨ True))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326110012477547337125612145501 : (p5 ∨ (p1 → (((False → (False → (p4 → p5))) → ((p5 → p2) → (((p2 → p3) ∧ True) ∧ ((p4 ∧ p2) ∨ (p5 ∨ p4))))) ∨ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310194337409433472915107210673 : (p2 ∨ ((p2 ∨ (((True ∨ (True ∨ ((True → p3) → p3))) ∨ p3) ∨ True)) ∧ (((p2 ∨ (p2 ∨ True)) ∧ (True → (False ∨ False))) ∨ (True ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156930295328940208684525699137 : (((((p3 → ((((((p1 ∨ False) ∨ p3) ∧ p5) ∧ p4) ∧ p1) ∧ p4)) ∨ p2) ∧ (True → p4)) ∨ p2) ∨ (True → ((p4 ∨ (p3 → True)) ∨ p4))) := by
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
theorem thm_5_vars_340718305583436591532533430342 : (p2 → (((p1 ∧ ((p5 → True) → ((p4 → ((((((p2 ∧ p4) → ((p3 → p2) → p5)) → True) ∧ True) → p4) ∧ p2)) → p4))) ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712485681291451839807235233894 : ((((((p2 ∧ True) → p3) ∨ (False ∧ p1)) ∨ ((p1 ∧ p2) ∨ (((p2 ∨ p1) ∨ ((p4 ∧ (p4 ∧ p2)) → p1)) ∨ ((p3 ∨ True) ∨ p3)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43777524534987077689927694888 : ((((False ∨ (((True → ((False → p3) → (True ∧ (((p2 ∧ (p4 ∧ (p3 ∨ p5))) ∧ True) → p3)))) ∨ True) → (p5 → p5))) → True) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336333391081344564758281332328 : (p1 → ((((p2 ∧ p2) ∧ True) → ((p4 ∧ (p3 → (((p2 ∧ ((p4 ∨ p3) → (p3 ∧ p3))) → (False ∧ p1)) ∨ p5))) ∨ (p1 ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134219984912548506695302675103 : ((((p5 ∧ (((False → p5) ∧ p1) → True)) ∧ (p3 ∨ (p2 ∨ ((p2 ∧ p1) → (p5 → ((p3 ∧ p5) → p4)))))) ∨ p3) ∨ (False ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641613880743926831148423795871 : (((((p5 ∧ p1) → (False ∧ ((((True ∧ p3) ∧ p1) ∨ ((((p1 → ((p5 ∨ p5) ∨ (p3 ∨ False))) → p3) → p2) ∧ p2)) ∧ p3))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150199407043876561226776545430 : ((p2 → (((True → ((False ∨ p1) → ((False ∧ (p2 → (p3 ∧ p4))) → (p5 ∧ p3)))) → p1) ∧ (p3 ∨ p1))) ∨ (((p1 ∧ True) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669904992619524240380288464096 : (((((p5 ∨ ((p3 ∨ (p5 → p3)) → (p5 ∧ ((False ∨ p4) ∧ p4)))) → ((p1 → p1) → ((p3 → p2) ∧ p5))) ∨ ((True ∨ p4) ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169028920662521758620816131013 : ((p2 → ((p2 ∧ ((((((p3 ∧ False) ∧ p2) ∨ p5) ∧ (p5 ∧ p4)) → p2) → True)) → p5)) → (((p4 ∨ p1) ∨ p4) → ((p5 ∨ p3) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184855421104357467812892722470 : ((((p3 ∨ p1) ∧ p1) ∧ (p4 ∧ ((False → p5) → (p1 ∧ True)))) ∨ (False → ((p5 ∨ (((p3 → True) ∧ (p2 → p5)) ∨ (True ∨ p5))) ∧ p4))) := by
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
theorem thm_5_vars_15154444964212465179938922777 : (((p2 ∨ (p3 → ((((((False ∨ (p2 → p1)) → ((p3 ∧ p3) → True)) → (p4 ∧ p1)) ∧ False) → p2) → (False ∧ p2)))) ∨ (p2 → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148483376909668961949246637246 : ((((p3 ∧ (p3 ∨ (p3 ∧ (p2 ∨ (p3 ∧ (True → p4)))))) ∨ p4) ∨ (True ∨ (((False → p1) → p4) ∨ p3))) ∨ (False ∧ (False ∨ (p5 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115937420998774191193329260210 : (((p5 ∧ (p2 ∧ (p4 ∨ p3))) ∨ ((p5 ∧ ((p3 → p4) ∨ p4)) ∨ (False ∧ (p2 → (p1 ∧ ((False ∨ p3) ∧ (True ∧ p5))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233186163871454261771835620921 : ((p5 ∧ (p4 ∨ True)) → ((p1 ∧ ((True ∧ (((p4 → ((p5 → (p5 → p2)) → False)) ∨ ((p1 ∧ p1) ∧ False)) ∧ p4)) ∧ (p4 → p5))) ∨ True)) := by
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
theorem thm_5_vars_320093455914626583050316220108 : (p4 ∨ (((p5 ∨ False) ∨ True) → ((False ∨ ((((p4 → p4) ∨ ((p3 ∧ p3) → ((p1 ∧ p1) ∨ True))) → False) ∨ (p3 ∧ (True ∨ p4)))) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119418433062318517510199897829 : ((p4 → ((p2 ∨ ((p3 ∧ (((False → p5) → p2) → (True ∨ ((False ∧ True) ∨ (False → False))))) → (p2 ∧ (p2 → False)))) → False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339798834721255994931725059234 : (p1 → (p5 ∨ ((p3 ∧ ((((p5 ∨ p4) ∨ (((p5 ∧ False) ∨ (p5 → p1)) ∨ (p2 ∧ p4))) ∨ p5) ∧ (p1 ∧ (p3 → p1)))) → (False ∨ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h6.left
        let h11 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h6.left
        let h14 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h6.left
          let h22 := h6.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h6.left
        let h27 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h6.left
    let h30 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39426025214895476208907995356 : (((p4 ∧ (p3 ∨ ((((p4 → (p3 ∨ (p3 ∧ p4))) ∧ (p4 ∨ False)) ∨ ((True → ((p4 ∧ p5) → (p4 ∧ False))) → True)) ∧ True))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64845841338372572834547895634 : ((p2 ∨ ((True → ((True ∧ p4) → ((((False → False) ∨ p3) ∧ p1) ∧ ((p4 ∨ (p2 → (p5 ∧ True))) ∨ (p5 → (p1 ∨ p2)))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204200194409612630496674466955 : (((((p4 ∨ True) ∨ True) → False) ∧ p3) ∨ ((p1 → ((p1 ∨ p5) ∨ ((p1 ∧ (p5 ∧ (p2 → p2))) ∨ (p3 → (True ∨ True))))) ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322929272126671095322119973716 : (p5 ∨ ((True ∧ (((True → (p5 ∧ ((p5 ∧ (p4 ∧ p3)) ∧ p2))) ∧ (p5 ∨ ((False → p1) → (p3 ∨ (p2 ∧ (p4 → False)))))) ∨ p5)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191499174264702315550733146533 : ((False ∧ (((p5 → ((p2 ∧ p2) ∨ p2)) ∧ p5) ∧ True)) ∨ ((((((True ∨ (p1 ∨ True)) ∧ p3) → p5) → False) ∧ p2) → ((False ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_327149246062112327998330222960 : (True → ((p3 ∧ (((p2 → (p2 ∨ p5)) → (p2 ∧ ((p1 → p3) → (((p2 ∨ True) ∨ (False ∨ (p3 → (p5 → p3)))) ∨ p1)))) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61007778174946484236126665040 : ((False ∧ (((False → (p4 ∧ True)) ∧ (p5 ∨ (p4 → (p4 ∨ (False ∨ ((p3 ∨ ((p2 ∨ False) → (p4 ∨ False))) → (p3 ∨ p4))))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149114001467880201205197055325 : (((True ∧ p3) ∧ ((p5 ∧ ((p3 ∨ True) ∧ False)) ∧ (p3 ∨ (((True ∨ p3) → p2) ∨ (p3 → (p5 ∨ p5)))))) ∨ (((True ∨ p1) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206357078069337592723465387416 : ((p2 ∨ ((p2 ∧ True) ∨ (p1 → p2))) ∨ ((((p4 → p4) ∧ ((p4 → (((p4 ∨ p5) → p5) ∧ ((False ∧ p1) ∧ False))) ∨ True)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232885859713731941657548193124 : ((p3 ∧ (True ∧ p3)) → ((p2 ∧ ((((p2 → ((p1 → (p1 → True)) → ((p4 → p2) ∨ (p3 ∨ p3)))) → p2) ∧ p2) ∨ p1)) ∨ (True → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804016712757091160701248571893 : (((p3 → (((p1 ∨ p1) ∧ (((p1 ∧ (p5 → (p4 ∨ (p4 → p1)))) ∨ ((True ∧ (False ∨ True)) ∧ p5)) → p4)) ∨ ((True ∧ True) → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186455908747017102000597508561 : ((((((p2 ∧ p3) → p5) ∧ (p5 ∨ p1)) ∨ True) ∧ (p5 ∨ p5)) → ((p3 → (p3 → p4)) ∨ (((p1 ∧ p3) → (True ∧ p3)) → (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Implications on the right can always be decomposed.
      intro h27
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54001546261467123299632387043 : (((((((p1 ∨ p2) ∧ (False → True)) → p5) ∨ True) → p3) → (((True → ((((p4 → True) ∧ p5) → p3) ∨ (p5 ∧ True))) ∨ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114396642078278748607829793764 : ((((False ∨ (((p5 ∧ (True → (p5 → p2))) ∨ p5) ∧ p3)) ∧ (p3 ∧ ((True → True) ∧ p4))) ∨ (False → ((False ∧ True) ∧ p1))) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42153598687047673963522865110 : ((((p1 → p1) → ((False ∧ ((p4 ∧ ((((p1 ∨ (p3 ∨ p4)) → (p5 → p1)) → (True ∧ False)) ∨ (p1 → True))) ∨ True)) ∨ True)) ∨ p3) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185498549631411040862660683595 : ((p2 ∨ ((((p2 ∧ p4) → True) → p1) ∧ ((p2 → p3) → p5))) ∨ ((p3 → (p3 ∨ ((p3 ∨ p1) → (False ∧ (True → (True ∨ p2)))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717665545824120755924320755931 : ((((((True ∧ True) ∧ p1) ∧ p5) ∨ (((((p1 → p5) → p2) ∨ ((p5 ∧ True) → (p3 ∧ False))) ∨ p4) → (p3 → ((p3 ∨ False) ∨ p4)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147352865315368979340675407392 : ((((p1 ∨ (p4 → (False → ((p3 ∧ (True ∧ (False ∧ p5))) ∧ (True → p3))))) ∧ ((p1 ∧ p2) ∧ p1)) ∨ p2) ∨ ((False ∧ (p3 → False)) → p4)) := by
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
theorem thm_5_vars_219206824193140441210619740418 : ((False ∨ (True → (p3 ∧ False))) → (((True → p5) ∨ (((p5 ∧ (p5 → p5)) → (False ∧ (p4 → (p4 → False)))) ∨ True)) → ((p3 ∨ p1) → p2))) := by
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
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h9 := h7 h8
        -- We need to get the right conjuct of h9 based on <expert-advice>.
        let h10 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h16 := h14 h15
          -- We need to get the right conjuct of h16 based on <expert-advice>.
          let h17 := h16.right
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h22 := h20 h21
          -- We need to get the right conjuct of h22 based on <expert-advice>.
          let h23 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h26 =>
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h29 := h27 h28
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h33 =>
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h36 := h34 h35
          -- We need to get the right conjuct of h36 based on <expert-advice>.
          let h37 := h36.right
          -- False on the left can always be used.
          apply False.elim h37
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h42 := h40 h41
          -- We need to get the right conjuct of h42 based on <expert-advice>.
          let h43 := h42.right
          -- False on the left can always be used.
          apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180274692792393828568429493509 : (((p2 → ((((p2 ∧ p4) ∨ (p3 ∨ (p3 → False))) ∧ p1) ∧ p3)) → p3) → ((p3 ∧ p1) ∨ (((True ∧ p5) ∧ p1) → (p1 → (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660058256954352065821773574204 : (((((((((p2 → p4) ∨ (p5 ∧ (p2 ∨ (p4 → (((p3 ∧ p3) → True) ∨ p3))))) ∧ p3) → p4) ∨ (True ∨ p2)) ∨ p2) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50492494593092423934974789815 : (((p5 → ((p3 ∧ ((p2 ∨ (p4 → (True ∨ (((True → True) → (p3 → p4)) → p1)))) ∨ p1)) → p1)) ∨ (((p5 → False) ∨ p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39570438442066665378541642633 : (((p1 ∨ (((((p1 ∨ p1) ∨ False) ∨ False) ∧ p2) ∧ (((False ∧ False) ∧ (p3 ∨ (p4 ∨ ((p3 ∨ (p5 ∨ p2)) ∧ p1)))) ∧ p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152390020529763303320811816268 : ((((p2 ∨ (True ∨ p4)) ∨ p2) → ((p4 ∨ (((False ∧ True) → True) ∨ (((p4 → p3) ∧ p4) ∧ False))) ∧ p4)) → (p4 ∨ (p2 ∨ (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (True ∨ p4)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54303821143496988592496527976 : ((((False → False) ∨ (p1 ∨ ((p4 → p4) → p2))) ∧ ((((((p2 ∧ (p4 → False)) → (p1 ∨ (False ∨ p4))) ∨ p3) ∨ True) ∧ p1) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779883400098196658480644777972 : (((p2 ∨ ((True → ((((p4 ∧ (p5 ∨ p3)) ∧ (p5 ∧ p2)) ∧ (((p5 → p4) → p5) ∧ False)) ∨ ((False ∨ p1) → (False ∨ True)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43298247143183224679475581439 : (((((p4 → (p1 ∧ ((p5 ∧ ((False ∨ True) ∨ p4)) ∨ ((p5 → (p4 → (False ∨ ((p3 ∨ False) ∧ p4)))) ∧ False)))) ∧ p1) ∨ p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60000150535832806447675745561 : (((False ∨ p4) → ((p5 → p3) ∧ (p5 → ((p5 → p4) → ((p5 → p3) → (p5 → ((p3 → (p3 ∨ p2)) ∧ (p4 ∧ (p1 ∨ False))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769136932424232885265669591136 : (((p5 ∧ ((p3 ∨ False) ∧ ((p3 ∨ False) ∨ ((((p4 ∨ (p4 → p2)) ∨ p4) ∧ (p1 ∨ ((True → ((False ∨ p1) ∨ p3)) ∨ p4))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64876845584027799103946285660 : ((p2 ∨ (((((p3 → False) ∧ (p2 ∨ p2)) → (p5 ∨ False)) ∨ (((p2 ∨ False) ∧ (((p2 → False) → p3) ∨ p2)) ∨ p5)) → (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40499913516430231816779850654 : ((((False ∧ ((p3 ∨ ((p5 ∨ ((p4 ∧ p1) ∧ ((p5 ∨ False) ∨ ((p4 ∨ p1) ∨ p1)))) ∨ ((p5 ∧ True) → p1))) ∨ True)) ∨ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720031745193810118918687125336 : ((((((p2 ∨ p4) ∨ p2) ∧ p5) → ((True ∨ True) → (True ∧ (((p3 ∧ (p3 → (p3 → (p1 → (p2 ∧ (p4 ∧ p4)))))) ∨ p3) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58991733353990835787953556048 : (((p3 ∧ False) ∨ ((p5 → (p5 → (((True ∨ p2) ∧ ((((p1 ∨ p5) → (p1 → p3)) → False) ∨ (p5 ∨ p5))) → False))) ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135074372461393764843174665788 : (((((p5 ∨ (((((True ∨ p4) → (p1 ∧ (False ∧ p4))) ∨ p3) ∨ p2) → p3)) ∧ p3) → (True → False)) ∨ (p5 ∨ p5)) ∨ ((p1 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51382985268180005016077714164 : (((((p5 ∧ ((((p1 ∧ p1) ∧ False) → p1) ∧ p3)) ∨ (((True → True) → p4) ∨ p2)) ∨ p2) → (p5 ∧ (p1 → ((p5 ∧ True) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328115151506683077428264166968 : (True → ((((p2 → (((True → ((p1 ∧ (True ∨ p4)) ∧ (False ∧ p1))) → p4) ∨ True)) ∧ p5) ∨ (p5 ∨ (p5 → p5))) ∨ ((p4 ∧ p4) → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193522421947400623948873981700 : (((p3 → True) ∨ (p1 ∨ ((False → p5) ∨ (True ∧ p5)))) → (((p3 ∧ (True ∧ (p4 → False))) ∧ p4) → (p2 ∨ (p4 → (p3 → (p1 ∨ False)))))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h18 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h19 := h8 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h24 := h8 h23
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135235024242405388149190787991 : ((((((True ∧ False) → p1) ∧ p4) → ((((False ∨ p1) ∨ (True ∧ p5)) → p5) ∨ ((p5 ∧ False) → True))) → (p1 ∧ p2)) ∨ (p3 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54575848071525607370077055753 : (((p1 ∨ ((((p5 ∨ p5) ∨ p4) ∧ True) → p1)) ∨ (((p4 → (((p3 ∨ ((p2 ∧ False) → p1)) ∧ (True ∨ p5)) → p4)) → p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346317067332918442199931926902 : (p3 → (((((p3 → (p3 → ((((((p4 ∧ p2) → p5) ∧ True) ∨ p5) ∧ p2) ∨ False))) → p4) ∨ (True ∨ p1)) ∨ (p1 ∧ p5)) ∨ (p2 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_678312685691813756774000427848 : (((((((p1 ∨ p4) → p2) → (p3 → (p5 ∧ False))) → (p4 ∨ (p3 ∨ ((True → p2) → (p5 → p1))))) ∨ (((p1 → p1) → p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129263707833752410793549127444 : (((((False → (p5 ∧ p2)) → (p2 ∧ p3)) ∨ (p4 ∨ (p5 → (p3 ∧ ((p3 → ((p2 ∨ p4) ∨ p3)) ∨ p5))))) ∨ True) ∧ (True ∨ (p2 ∧ p4))) := by
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
theorem thm_5_vars_184235483605632399481043528853 : ((((((p4 ∨ ((p1 → True) ∧ True)) ∨ p5) ∨ p2) → p3) → p4) ∨ (((False ∧ (p5 → (True → False))) ∧ ((True ∨ p3) → (p3 ∧ p4))) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259876917596981387599420106521 : ((p1 → p4) → ((p3 → ((((False ∨ p2) ∨ p5) ∨ (((False ∧ (p5 ∧ p1)) ∨ p5) ∨ True)) ∨ True)) ∨ ((((True ∨ p2) → p3) ∧ p5) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691828501328824447452989413639 : ((((p5 ∨ (p5 ∧ (p5 → ((p5 → (((p4 → False) → False) ∨ p4)) ∨ (p4 ∨ p1))))) → ((p1 → ((p2 → p4) ∧ (p4 ∧ False))) ∨ True)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350970470022100220331279128252 : (p4 → (((p3 ∨ (p2 ∨ (p4 ∨ False))) ∧ (True → (p4 → (((p5 → p4) ∧ p3) ∨ (((p2 ∧ False) → p5) ∧ (p4 ∧ p3)))))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200592344589566806196383452248 : ((True ∧ ((True ∨ p1) → (True → (p4 → True)))) → (((p2 ∨ False) → False) → (p2 → (((p5 ∧ (p1 → True)) ∨ p5) ∧ (False → (True ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173081434251720554931413121862 : ((p1 ∨ (((p5 → (((p3 → False) ∨ True) ∨ (p2 → (p2 → p1)))) → p3) → p5)) ∨ (p5 ∨ (True ∨ (p5 ∧ (p2 ∨ ((True ∧ p2) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67512179321471915847294104977 : ((p1 → ((False ∨ (((p4 → p3) ∧ p5) ∨ (False → p4))) → ((p1 ∨ (p2 → (p3 ∧ p4))) ∧ (((p4 → p5) ∨ True) → (p3 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262402783195963572095247310948 : (True ∧ (((p4 → True) → (p5 → ((p2 ∧ (p4 → ((((p5 ∧ (p3 ∨ p4)) ∧ p1) ∧ ((p4 ∧ False) → p2)) → (p3 ∨ False)))) ∧ True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314823815963529092731894797468 : (p3 ∨ ((((False ∨ p3) ∧ ((p4 ∨ ((p3 ∧ p3) ∧ p4)) ∧ True)) ∧ p2) ∨ (((p1 ∧ p5) ∨ (((p3 → p1) → p1) ∨ True)) ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_148778485582710957971392456643 : (((((True → False) → p4) → (p3 ∨ False)) ∨ (True ∧ (((p2 ∧ (p4 ∧ p3)) ∨ (False → True)) ∧ (p3 ∨ True)))) ∨ ((p5 → (p5 ∨ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



