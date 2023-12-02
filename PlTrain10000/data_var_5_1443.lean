variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51991406871916939302078185320 : ((((False ∨ p4) → ((((p1 → (p5 ∨ p3)) ∨ (False ∧ (p2 → p2))) ∨ p2) → False)) ∨ (p1 → ((((p2 ∧ p2) ∧ p1) → p2) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240450144730438925174117478166 : ((p5 ∨ True) ∧ ((p4 ∧ ((p1 ∨ (True ∨ p3)) ∧ p2)) ∨ ((((p5 ∨ p3) ∨ True) ∨ ((((True → p5) → p1) ∧ p1) → (p1 ∨ p1))) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40886573313534250614228295476 : ((((((p4 ∨ p4) ∧ (((p4 ∧ False) ∧ (p2 → p1)) → False)) → ((((p5 → p5) → p1) ∨ p4) ∧ (p1 ∨ p4))) ∧ (p4 → True)) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207153101228655775502230685916 : (((p2 → ((p2 ∧ True) → p5)) ∧ p2) → ((False ∨ p3) → (((p3 → False) ∨ (p3 ∧ (p3 → ((p1 ∧ True) ∧ ((p1 ∧ p4) ∧ p1))))) → p4))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h18 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h19 := h13 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207524113690286263541070946641 : (((((p4 → p2) → p2) ∧ True) → False) → ((p2 ∨ ((True → p2) ∧ p4)) → (((p2 ∨ ((p1 ∧ p3) → (p1 ∧ p3))) → p1) ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 → p2) → p2) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (((p4 → p2) → p2) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h10
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166433313105273586708996291885 : ((p1 ∨ (p2 ∨ ((((p3 → p3) → p2) ∧ ((p4 ∧ p2) ∧ (p5 ∧ (p2 ∧ False)))) ∨ False))) ∨ (p5 ∨ ((p5 → ((True ∧ p4) ∨ p5)) ∨ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53345786519499393991262107406 : ((((True ∨ (p2 ∨ ((((p3 ∧ p4) ∧ p2) ∨ False) → p3))) ∧ p4) → (p5 ∨ ((p1 ∧ (p3 → p2)) → ((False ∧ p4) ∨ (True ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43193427866595865463626867608 : (((((True → True) → (True ∧ (p2 → (((p3 → (((p2 → p4) → p1) ∧ p5)) ∧ False) → (p1 → ((p5 ∨ p2) → p2)))))) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58512169672313283994492089749 : (((p5 ∨ True) ∧ (((((p4 ∧ p2) ∧ ((False ∨ False) ∧ p4)) ∨ p3) → (p5 ∧ ((p1 ∨ ((p1 → (p1 → p2)) ∧ p2)) → False))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149324121758259293673247547070 : (((p4 ∧ p5) → ((((True ∧ ((p5 ∧ (p1 ∧ True)) ∨ (p2 ∨ p3))) ∨ ((p2 ∨ p3) ∧ p3)) ∧ True) ∨ False)) ∨ ((True ∧ (p2 → True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198417900644180722271186959952 : ((p4 ∧ ((p5 ∧ (False ∧ p3)) ∨ (p5 → p1))) ∨ ((False ∨ ((p4 → ((p2 → (p1 ∨ p4)) → (p2 ∨ False))) ∧ (False → (p2 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306616314441552955062464852905 : (p1 ∨ ((p4 → True) → (p4 → ((((p1 ∨ p5) → ((p1 ∨ (p1 → ((p5 ∨ p1) ∨ (p4 ∧ ((False → p2) ∨ True))))) ∧ p5)) ∧ p2) ∨ True)))) := by
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
theorem thm_5_vars_305202774191250707317182085631 : (p1 ∨ ((((p4 ∧ (p4 ∨ ((p2 ∨ True) → p5))) ∨ ((True ∧ ((p5 ∨ (p4 ∧ p1)) → p2)) ∨ p3)) ∧ p3) → ((True ∧ False) ∨ (True ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633900150577990474083449828109 : ((((((False ∧ ((p2 → p5) ∨ (((True ∨ (False → True)) → (((p1 ∨ False) → (False ∧ p1)) ∨ p3)) ∧ p4))) ∨ p5) → (p4 → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172031454536097236611390806210 : (((p1 ∧ ((p1 ∨ p5) → (p1 ∨ (p3 ∨ ((True ∧ p1) ∧ False))))) ∨ (p1 ∧ False)) ∨ ((((p4 ∨ p2) ∧ False) ∧ p4) → ((False ∨ p3) ∨ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46331872638202848291869075312 : ((((True ∧ ((p5 → ((p2 → (True ∧ p2)) ∧ (True ∧ p3))) → ((p3 ∨ p1) ∨ p1))) → ((p5 ∨ (True ∨ p5)) ∧ p5)) ∧ (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119296511637507280318330514693 : ((p3 → (((((p3 ∧ p3) → (True → (True → p2))) ∧ p3) ∨ (((p1 ∨ (p1 ∨ (p3 → True))) ∨ (p5 ∨ True)) ∧ True)) → p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114030045721040714728227846481 : (((((((((p4 ∧ p2) ∨ ((p4 → p4) ∨ False)) → p1) ∧ (p4 ∨ p1)) ∧ False) → (p2 ∧ p5)) → False) ∨ (True ∨ (p5 → p2))) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328400962569306196058393411152 : (True → ((((((True ∨ (p4 ∨ (((p1 → p3) ∨ p4) ∧ True))) → p1) ∧ p2) ∨ (False ∨ p5)) ∧ p4) ∨ ((p5 ∨ p4) ∨ (True ∨ (p4 → p1))))) := by
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
theorem thm_5_vars_119293795525988231493136754256 : ((p3 → (((p4 ∧ (False ∧ ((False ∨ (p2 ∧ p2)) ∧ ((p4 → ((((p5 ∨ p1) ∨ p4) ∨ p1) ∧ p1)) → p2)))) → p2) → p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299105247954499355014407177558 : (False ∨ (((((p5 → True) ∧ False) ∨ (((p2 ∨ ((p2 ∨ ((p4 ∧ False) ∨ p2)) ∨ (p5 ∧ p4))) → (p3 ∨ p1)) ∨ (p1 ∨ True))) ∧ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37421507199516050589988585912 : ((((((p1 ∧ (p3 ∨ ((p5 ∨ p4) ∨ ((p1 ∨ p1) ∨ ((p5 ∧ (p1 → p4)) → p2))))) → p4) ∧ ((p3 → p4) ∨ p5)) ∨ False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156607624019608484534789534239 : (((((False → p5) ∧ ((((False ∧ True) → (p2 ∧ p1)) → ((p5 ∨ p5) → p2)) ∨ p4)) ∧ p1) ∧ False) ∨ ((True ∧ ((True → p3) ∧ p1)) → p3)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737619272495054412300074246177 : ((((p5 → p2) ∧ ((p1 ∨ p2) ∧ ((((p4 ∨ p1) → ((p2 → (p1 ∧ (False ∨ p4))) ∨ (True ∧ (p5 ∨ False)))) ∨ p3) ∧ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630449150783073215573680373820 : (((((True ∨ (((p2 ∨ ((p1 ∧ p3) ∨ p5)) ∨ ((p5 ∨ p3) ∧ ((False ∨ p2) ∧ (p3 → (p3 → (p2 ∧ p1)))))) → p4)) ∨ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81224572809963523551345123891 : (((p4 ∨ (((True ∨ (p5 ∨ True)) → p4) ∧ (p3 ∧ ((False → p5) → (((p3 ∧ (p3 ∧ p5)) ∨ p1) ∧ False))))) ∧ ((p5 ∨ p3) → p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ (p5 ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113448700960928376707322265025 : ((((True → ((p2 ∨ (((False → (True ∧ (p4 ∨ False))) → (p2 ∨ p5)) → (p5 → (p2 ∨ p5)))) → p4)) ∨ p2) ∨ (False → p4)) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114527502740738642976197956723 : (((p1 ∨ (((True ∨ ((p3 → p1) ∨ p3)) → (p3 ∨ (p2 → ((True → True) ∨ p3)))) ∨ True)) → ((p1 ∨ p4) ∧ (p3 ∨ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257549697348141871282983818858 : ((p3 ∨ p1) → (((((((p2 ∧ True) → p1) → False) → p3) → (False ∧ ((False ∧ p3) ∨ (p2 ∧ (True ∨ True))))) ∧ (p5 ∧ (p2 ∨ p2))) ∨ True)) := by
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
theorem thm_5_vars_167546064879562040748010269329 : ((((((False ∨ (False ∨ ((p3 ∨ True) → True))) ∨ p2) ∨ (p2 ∨ p1)) ∧ p2) ∨ (p3 ∨ p3)) → (p1 ∨ (True ∨ (False → ((p2 ∨ p4) ∧ False))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- False on the left can always be used.
            apply False.elim h9
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623031678407993490473311762239 : ((((p5 ∧ (p4 ∧ ((p2 → True) ∧ (((p5 → True) ∨ p3) → ((p2 ∨ p1) ∧ (((p2 ∧ p1) → ((False ∨ p1) → p2)) ∧ p5)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_112165331522136950781985513003 : (((p3 ∧ ((p5 ∧ (p2 ∨ (p3 ∧ ((True → (p3 ∨ True)) → (p5 → (False ∧ (False → (True ∧ p5)))))))) ∨ (p4 ∨ p5))) ∨ True) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68230880620047327362891328778 : ((p3 → ((((((True ∨ False) ∨ p3) ∨ (False ∨ p5)) → p1) ∧ ((((p5 → p5) ∨ True) → p2) → (p5 ∨ ((True ∧ False) ∨ p5)))) → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((True ∨ False) ∨ p3) ∨ (False ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118707346413336039850267242975 : ((p5 ∨ ((((p1 ∧ p4) ∨ p5) → ((p3 ∧ ((p4 ∧ p1) → ((p4 → (True ∧ True)) ∧ ((p1 ∧ p2) ∨ p3)))) ∧ False)) → False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788377746230164910608689854716 : (((p5 ∨ (((((p2 → ((True ∨ p1) ∧ ((p5 ∧ p2) ∨ ((p2 → False) → (p2 ∨ p1))))) ∨ p2) ∨ (p4 ∨ p2)) → (p3 ∨ p1)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133726748389047985782156157255 : ((((((p5 ∧ (p1 ∧ True)) → p3) ∧ (p2 ∨ (p4 ∨ (False ∧ p3)))) → (False ∧ ((p2 ∧ (False ∨ p1)) → p3))) ∧ p2) ∨ (True ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47899671372127763799316354376 : ((((False → (((p3 ∨ ((p2 ∨ p1) ∧ p5)) ∧ (((True ∧ (p5 ∧ (p2 ∨ False))) ∧ p4) ∨ p4)) ∧ True)) ∨ (p2 → False)) → (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763110785049869279658673025596 : (((p3 ∧ (((False ∨ p3) ∨ p2) → ((p5 ∨ True) ∧ ((((p4 ∨ p4) ∧ (False ∨ p4)) → (p5 ∨ (p5 ∧ p3))) ∨ ((p2 → p3) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37767244677098822010607410124 : ((((((p3 → False) → True) ∨ ((((((False → p3) ∧ p5) ∨ (p2 → p4)) ∨ p2) ∨ (p4 ∧ p5)) → ((p1 ∨ True) → False))) → p1) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169015159304518034942716068843 : ((p1 → (p1 ∨ (p2 → ((p2 ∧ p4) ∨ ((p4 → ((p2 → False) ∨ (p5 → False))) ∧ p5))))) → ((((p5 ∧ p5) → False) ∧ (p4 ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46018931904410125420188763628 : ((((((p2 ∧ p4) ∨ p1) ∧ ((p1 → p5) ∨ ((p4 ∨ (False ∨ ((p1 → ((p5 ∨ p4) → p2)) ∧ p5))) ∨ p4))) ∧ True) ∧ (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116266209564259978057138047146 : (((p3 ∧ (p5 ∧ p4)) ∨ ((((p5 ∧ False) → p2) → ((p3 ∨ (p4 ∨ p3)) → p5)) ∨ (False → ((False ∨ (p5 ∧ True)) ∧ p4)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352813146102861227129545406214 : (p4 → ((p5 ∨ False) → (((((True ∧ p1) ∨ ((((((p5 → p2) ∧ p3) → p2) → p3) ∧ p4) ∧ p4)) ∧ (p2 ∧ (p1 ∨ False))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167708263354367004582428349391 : (((p4 ∧ ((True ∧ ((p4 ∨ True) ∨ ((p3 ∨ p2) ∨ p5))) → False)) ∧ (p5 → (p1 → p5))) → (True → (False ∧ (p3 → ((p1 ∨ True) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (True ∧ ((p4 ∨ True) ∨ ((p3 ∨ p2) ∨ p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (True ∧ ((p4 ∨ True) ∨ ((p3 ∨ p2) ∨ p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171328709111618400126180456997 : ((((p1 ∧ (p3 ∨ (((p1 ∨ False) ∨ p2) ∨ ((False ∨ p4) ∨ False)))) ∨ p4) ∧ False) ∨ (((False ∨ True) → p3) → (True ∨ (p1 ∨ (p4 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39781677425797818255915628045 : (((True → (p5 ∨ ((p4 ∨ p1) → (p2 ∨ (p2 ∨ (((p5 ∧ True) ∨ (p3 ∧ ((p1 ∨ (True ∨ p2)) → (p3 ∧ True)))) ∧ p4)))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68576642401376879178168344053 : ((p4 → (((((p3 ∨ (p2 → (p4 ∧ p5))) ∨ (p3 ∧ p1)) → p1) ∨ (p3 ∧ ((((p4 ∨ p5) ∧ p3) → (p2 ∧ True)) → True))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356041194917707081850999162798 : (p5 → ((True ∧ (p4 ∨ (p2 → (p3 ∧ ((p2 ∧ ((False ∨ p2) ∧ (p5 ∨ p3))) → ((p4 → p5) → p4)))))) ∨ ((p1 → (p1 ∨ False)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304697220554720991551373718411 : (p1 ∨ (((((p5 → (p3 ∨ p3)) ∨ ((p5 ∨ p5) → (False → ((p1 ∨ ((True ∨ (p4 ∧ p4)) ∨ p3)) → True)))) → p3) → p1) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327155119098778624635110050712 : (True → ((p4 ∧ ((((p1 → ((True ∧ ((p5 ∨ (False → (p4 ∧ False))) ∧ (p1 ∧ (p3 ∧ (p5 ∧ p5))))) ∨ p2)) ∨ p3) ∨ True) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41645504470013214440573530186 : (((((((p4 ∨ False) ∨ True) ∧ p3) → p1) ∧ ((((((p1 → p4) ∧ ((True ∨ True) ∨ p4)) → p5) ∨ True) → p3) → (p5 → p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663471139683326258457621925722 : (((((False → True) → ((((p3 ∨ False) → True) → (p5 ∧ (True ∧ False))) → (p4 ∨ (p3 ∧ (p5 ∨ ((p1 ∧ True) → p4)))))) → (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658029237980586301068947557227 : ((((p2 ∧ (p5 ∨ (p4 ∨ ((p4 ∨ p2) ∨ ((((p1 ∧ p3) → (p2 ∨ (p5 ∧ True))) → p5) ∧ ((p2 → True) ∧ p2)))))) ∨ (p1 → p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_115495577399071161159032219249 : ((((p1 ∨ (p3 ∧ (False ∧ (True → False)))) ∨ p3) → (p4 ∨ (p1 ∨ (((p4 ∨ ((p4 → p3) → p2)) → False) ∨ (p2 ∨ p3))))) ∨ (False ∧ p5)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327804717090233059672519581141 : (True → ((((p2 ∨ ((p4 ∧ (True ∧ p4)) ∧ p4)) ∨ (p2 ∨ ((p1 ∧ (p4 ∨ (False ∨ ((p4 → p1) ∨ p1)))) → True))) ∨ p1) ∨ (p4 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614431195417570828051581284465 : (((((p4 → (((p1 ∨ (False ∨ False)) ∨ p3) ∧ (p1 → (p3 ∧ (((p4 ∨ p5) ∨ p5) → (False → p2)))))) → ((False → p5) ∧ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60403008393207038389381214383 : (((p4 → True) → ((((p4 ∨ ((((False ∧ p5) → (p3 ∧ p1)) ∧ p4) ∨ p1)) ∨ (((True ∨ True) → p4) ∧ p4)) ∨ p2) ∨ (p1 → p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165625769055715416757825035909 : (((((p5 → (p5 ∧ p4)) → False) → p4) ∧ (p3 ∨ ((p2 ∨ (p2 ∧ (False ∨ p2))) ∧ False))) ∨ (p1 ∨ ((p1 → True) ∨ ((p1 → True) ∧ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20481647146074518282942355775 : ((((p4 → p1) ∧ (((True ∨ False) ∧ ((p4 ∨ p2) → False)) ∧ (False → p4))) → (((True ∧ False) ∨ (p1 ∨ ((True → False) → p4))) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300150506009499338175073473972 : (False ∨ ((p2 ∨ (((p2 → ((False → ((p4 ∨ p5) ∨ p3)) → (((((p5 ∨ True) ∧ p2) ∧ p4) ∨ False) ∨ p5))) ∨ p1) → False)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345471388375948085339295016086 : (p3 → ((((((p4 ∧ p3) ∨ (False ∨ (p3 → ((p1 ∨ p3) → (False → p5))))) → p1) ∨ ((p2 ∨ p4) → p2)) ∨ ((p2 → p3) ∧ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213807558887365803512377739185 : (((p3 ∧ (p1 ∧ p4)) ∨ p5) ∨ ((((((p1 → True) → (((p5 ∨ p2) ∨ p5) ∨ p1)) ∨ p4) → True) → (False ∧ p5)) → (p3 ∧ (p5 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → True) → (((p5 ∨ p2) ∨ p5) ∨ p1)) ∨ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((((p1 → True) → (((p5 ∨ p2) ∨ p5) ∨ p1)) ∨ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790690933296338994120717735429 : (((p5 ∨ (p5 ∨ (((((p3 ∧ p3) → p1) → False) ∨ p3) → (p5 ∨ (((p3 ∨ False) ∨ (p5 ∨ p3)) → (p3 → ((p1 → p2) ∨ p3))))))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340886580358131063354600397707 : (p2 → (((((p4 ∨ p1) → ((True → p3) ∨ (False ∨ ((False ∨ p4) ∧ p3)))) → p5) ∨ (False ∧ (p1 ∨ ((True → (p3 → p2)) → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182100857994897509056036134998 : (((False ∨ ((p4 ∨ True) → ((p2 ∨ p2) → (True ∨ p3)))) ∨ p2) ∧ ((True ∨ p3) → ((False ∧ ((p4 ∧ (p3 ∧ p1)) ∨ (True ∧ p3))) ∨ True))) := by
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
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44291516476615125097137347009 : ((((((p3 ∧ (p1 → (p4 ∧ (p4 ∨ p3)))) ∧ p5) → ((p3 ∨ p5) → (False ∧ p5))) ∧ ((p2 ∧ (True → (True ∧ True))) ∧ p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659122741867143810412694788082 : ((((p3 → ((False ∨ ((((p5 → (p2 ∨ p2)) → p5) → (False ∨ True)) ∨ ((p1 → (False ∧ p3)) ∨ (True ∨ p3)))) ∧ False)) ∨ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185518584460839156612695999107 : ((p3 ∨ ((p2 → (((True ∧ p1) ∨ False) ∧ (p3 ∨ True))) ∧ False)) ∨ (p5 ∨ (False → ((p2 → (False ∧ (True → True))) ∨ ((False ∧ True) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719449685055849095044503871232 : ((((p1 ∨ ((p2 ∨ p3) → p5)) ∨ ((((((p4 → p4) → p3) ∨ p3) ∧ p3) → (p3 → ((p3 ∧ (False ∧ p4)) ∧ (p4 ∨ False)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49824313085656850181117157313 : (((p3 → ((((p2 ∨ (False ∨ p3)) ∨ ((p1 → (((p3 ∨ p3) → p5) ∧ (False → p4))) → p4)) → p2) → p2)) → (p3 ∧ (True ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37329372838081238518632559587 : ((((((p1 → ((p2 → p4) ∧ ((((p1 ∧ (p3 ∨ p3)) ∨ True) ∧ True) ∧ (p3 ∧ (p1 → False))))) ∧ (False ∧ False)) ∧ p3) ∨ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181381910587730572097132984494 : ((p1 ∨ (((p5 → False) ∧ (p5 → (p5 → p2))) ∨ ((p2 → p4) → p1))) → ((((p2 ∨ p3) ∨ (p2 → (p2 ∧ True))) ∧ p4) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107887185966494160080667394841 : (((p4 ∨ False) ∨ ((((p4 ∨ (p1 ∨ (p2 → ((False ∧ ((True ∧ (p3 → p4)) ∧ True)) ∨ p1)))) ∨ p5) → (p2 ∨ p1)) ∨ True)) ∧ (p5 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63442124168735506842244121210 : ((p5 ∧ (p3 → (((False → (False ∨ p5)) → False) ∨ (((((False ∨ p2) → False) ∧ (False → False)) ∨ ((p2 ∨ p3) → p2)) ∨ (p4 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49370639751585328998306138198 : (((p4 → ((p5 ∧ True) → (((p5 → (p4 → (p1 ∨ p3))) ∨ p2) ∧ (((True ∨ (p1 ∨ True)) → p5) ∧ p1)))) ∨ (p4 ∨ (p3 ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_116753175737849770133116260420 : (((p5 ∧ p3) ∨ (((((p2 ∨ (p5 ∧ (((p2 ∧ True) ∧ (False ∧ False)) → False))) ∨ False) ∧ ((False → p1) → p5)) → p1) → p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310614738034456854775598242642 : (p2 ∨ (((p3 ∨ (p1 ∧ p3)) ∨ p5) ∨ (((False → (p5 ∧ ((p2 → p5) → p3))) ∧ (False ∨ p3)) → ((p4 → (p4 → p1)) ∨ (False ∨ p3))))) := by
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
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262402145190020224266535274638 : (True ∧ (((p2 → p5) → (((p4 ∧ (p4 ∨ p1)) ∧ ((False ∨ p5) ∧ (p1 ∧ p4))) ∧ (False ∨ (((True → p3) ∧ (p4 ∨ p4)) ∧ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192901894680570057746385181854 : (((p3 → ((False ∨ (p4 → False)) → p3)) ∧ (p4 → p1)) → (True ∧ (p1 → (p1 ∧ ((p2 ∧ True) → (((p5 ∨ p2) ∧ p2) ∧ (False ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h14 := h5.left
  let h15 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55188348287051184601161493196 : ((((True ∧ ((True → p3) → p5)) → False) ∨ (((((p3 ∧ False) ∨ (True → (p3 ∨ p4))) ∧ True) ∨ (p2 → (p2 ∧ (p3 ∧ True)))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149700280438378601259398326762 : ((p5 ∧ ((False ∨ (p1 ∧ p5)) ∨ (p3 ∨ ((((p3 ∧ p3) → ((False → p4) ∧ (p3 ∧ p5))) → p5) ∧ p5)))) ∨ ((False → p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52081950681837301469767521548 : ((((p5 ∨ ((True ∧ (p3 ∧ (p3 → (((p1 → True) → p1) → False)))) → False)) ∧ p4) → ((((p3 → (p5 ∨ False)) ∨ p1) ∨ p2) ∨ p4)) ∨ p3) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347024602616452037809498559891 : (p3 → ((p4 ∧ (((p1 → p2) ∨ (p1 ∧ (False ∧ p4))) → (p5 → ((False ∧ True) ∨ p2)))) ∨ (True → (p5 ∨ (p2 → ((p4 ∧ p3) ∨ p3)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113505862324911347439293070139 : (((((((p5 ∧ p1) ∨ (p4 → True)) ∨ p1) ∧ (((True ∨ p5) → p1) → p5)) ∨ (p3 → ((p5 ∧ p2) → p5))) ∨ (False ∧ p3)) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_46891181563337285261504116222 : (((((p3 → (((((p4 → p1) → (False → (p3 ∨ (p4 → (False ∨ (p3 ∨ p2)))))) → p2) ∧ p1) ∨ False)) ∨ p4) ∨ True) ∨ (p2 ∧ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135053036906212569829647007147 : ((((p5 ∨ ((((False ∧ (p3 → p5)) ∧ (p5 ∨ p2)) ∧ (((p1 ∧ True) ∧ p2) → p5)) ∨ p5)) ∨ True) ∨ (p4 ∧ p3)) ∨ (p1 ∨ (p4 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69526710881716483341270390730 : ((((((True ∧ p4) → ((p5 → p1) → (((p1 → p5) ∧ p2) ∨ ((p4 ∧ p5) → p4)))) → (False ∧ ((p3 → True) ∨ True))) ∧ p2) ∧ True) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∧ p4) → ((p5 → p1) → (((p1 → p5) ∧ p2) ∨ ((p4 ∧ p5) → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h14 := h4 h6
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_985378211130556434286156136649 : (((p2 ∧ (((False ∨ ((False ∧ p2) ∨ (False ∨ ((((p4 ∨ (p2 → False)) ∧ ((p4 ∧ p4) ∨ False)) ∨ (True ∧ False)) ∨ True)))) ∨ p2) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((False ∧ p2) ∨ (False ∨ ((((p4 ∨ (p2 → False)) ∧ ((p4 ∧ p4) ∨ False)) ∨ (True ∧ False)) ∨ True)))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204663389635447537517342527802 : (((p5 ∧ ((p1 ∧ p5) ∨ True)) ∨ p3) ∨ (p4 → (p5 → (p4 → (True → ((True → ((p2 ∨ False) ∨ (p4 → ((True → False) → p3)))) ∨ p5)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620343546028978785711447869763 : (((((p2 ∨ False) ∨ (p2 → (((((p1 ∨ True) ∧ ((((p4 ∧ False) → p5) → False) → p2)) → p3) → (p5 ∨ (p4 ∧ p3))) → p4))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136761611408555406257374156777 : (((p3 ∨ p4) ∧ (((p5 ∨ (p3 ∧ p3)) → (((p4 → (p3 → ((False ∨ False) → p1))) ∨ p1) ∧ (p4 → p5))) → p5)) ∨ ((False ∧ p4) → p2)) := by
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
theorem thm_5_vars_674290157750454440764986838589 : ((((False ∨ (((((True → (p3 → ((p3 → p2) → False))) ∨ False) → p4) → (p3 ∨ ((False ∨ p2) ∨ p1))) ∧ p5)) → ((p3 ∨ p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50176170627026019725686553120 : ((((((((p4 ∧ (p5 ∨ p1)) ∨ True) ∨ False) ∧ ((p4 → True) ∧ ((p3 → p1) ∨ False))) → p3) ∧ p4) ∨ (p3 ∨ (p3 → (p3 ∨ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46987055452610424237516064097 : (((((((p5 ∨ True) → (p1 → p3)) ∧ (((p2 → (p5 ∧ p5)) ∧ p5) ∧ p1)) ∨ ((p3 ∨ p4) → (p3 → False))) → p2) ∨ (p1 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133864017066749599848790983600 : (((p2 ∧ (((p5 ∧ (p2 → (p2 ∨ p3))) ∨ p3) ∨ ((p5 ∨ (((p5 ∨ p3) → p2) ∧ (p2 ∧ p2))) ∨ p5))) ∧ p4) ∨ ((p4 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227985953553706997010038049068 : ((p3 ∧ (p3 ∨ False)) ∨ ((p5 → (p4 ∧ False)) ∨ ((p5 → (p1 ∨ ((p2 ∨ (p5 ∨ p2)) → p5))) ∨ (p2 → (p5 ∧ ((p5 ∨ p2) ∧ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111761518848759110778762400795 : ((((((p5 → (p5 → (p4 ∨ ((True ∨ p3) → ((True → p2) ∧ p5))))) ∧ (True → True)) → (p4 ∧ p5)) ∧ (True ∨ True)) ∨ p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592122967820679507068897470563 : (((((p2 → (((p5 → (((((p3 → (False ∨ (p3 ∨ True))) ∧ p4) ∨ p1) ∧ p4) ∧ (True ∨ False))) ∨ p3) ∨ p3)) ∨ (True ∧ p4)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606455177605152639198114974875 : ((((((p4 ∨ (True ∧ (((((p3 → ((True → (p4 → (p2 ∧ p3))) → (p5 ∧ False))) ∧ p2) ∧ p3) ∨ p3) ∨ p4))) ∨ p1) ∧ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712863967480838898478796717773 : (((((True → p3) → ((p5 ∧ True) ∨ p5)) ∨ (((((p2 → (p4 ∧ False)) → False) → p3) ∧ (p4 ∨ p5)) ∨ (((False → True) ∧ p5) → p5))) ∨ p5) ∧ True) := by
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



