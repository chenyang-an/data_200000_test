variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699072539876539570115013199532 : ((((p3 ∨ (p5 ∧ ((p2 ∨ (((p4 ∨ p4) → False) ∧ p4)) ∧ False))) ∨ ((False ∧ (p5 ∨ ((p2 ∨ p3) → (False → False)))) → (False → p3))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328805977420542879933684374020 : (True → ((p4 ∨ (False ∨ (p5 ∨ ((True ∨ (p1 → p1)) ∧ p3)))) ∨ (((((p3 ∨ ((p1 ∧ True) → (p1 ∧ p1))) → p3) ∧ p2) ∧ True) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ ((p1 ∧ True) → (p1 ∧ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h13 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178422403625322116535815560575 : (((False → ((p1 ∨ (p4 ∨ (p1 ∨ (p2 ∨ True)))) ∨ False)) → (p3 ∧ p5)) ∨ (((p2 ∧ True) ∨ ((p5 → True) ∧ (p2 ∧ p4))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172190242563962517337445095685 : (((((p4 ∨ (((p2 → p2) → p1) → False)) → p4) ∧ True) → (p2 → (False ∧ False))) ∨ ((p1 → p1) ∨ (p2 ∨ (((False ∨ p3) → p5) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45698547282832686537304026097 : (((True → (((((p3 → p3) ∧ p4) ∧ ((True → (p4 ∨ p2)) → (((((p1 ∧ p2) → p2) ∧ p5) ∨ False) → p3))) → p2) ∧ p3)) → p3) ∨ p2) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209505766184442342858163776804 : ((p4 → ((False ∧ (p1 ∧ p5)) ∧ p1)) → ((((False → p1) → ((((p2 → ((False ∧ p3) → p3)) → False) → False) ∨ True)) ∧ p5) ∨ (p4 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320313874173421495157225021586 : (p4 ∨ ((p1 ∨ p3) ∨ (((((((True → (False ∧ (p3 ∨ p2))) ∧ p1) → (p5 ∨ p5)) ∨ p3) ∧ True) ∨ (p3 → p4)) ∨ ((p5 ∨ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301499608597888260619956403766 : (False ∨ ((p1 ∨ (p2 → True)) ∧ (p4 ∨ (((True ∨ p3) ∧ (p2 ∨ ((True → p1) ∨ ((p3 ∧ p4) → (True → p1))))) ∨ ((p4 → p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37956527482623448047197753261 : (((((p1 → (p2 ∨ ((p5 ∧ p2) ∨ ((((p5 ∨ p4) ∧ (p3 → (p1 → True))) ∨ False) → (p4 → p2))))) ∧ True) ∨ (True ∨ True)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41579312800520890263362894498 : (((((p3 ∧ (p5 → ((p2 → True) → p3))) → p3) ∧ ((p2 ∨ (p4 ∧ (p5 ∨ ((p1 ∧ p4) → p2)))) ∧ (p4 ∨ (p1 → False)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621019265128741995404761531771 : (((((False → p2) → (p4 ∨ ((p5 ∧ (p2 ∨ (p1 ∨ (((False ∧ p5) ∨ ((p2 ∧ True) → False)) ∨ (p4 ∧ (True → p2)))))) ∧ p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173567940694692548984902320559 : ((((p3 → p3) ∧ (p1 ∨ (((p5 ∨ ((p5 ∨ True) ∨ True)) ∧ p3) ∧ False))) ∧ p1) → (p1 → ((((p1 → p4) → p3) ∨ (True ∧ p2)) ∨ True))) := by
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
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50221673961368516517080998240 : (((((p5 ∨ p2) → ((p2 → ((p3 ∧ (p2 ∨ p4)) ∧ False)) ∧ ((p3 ∧ (p2 ∧ True)) ∧ p4))) ∨ False) ∨ (p3 ∧ (True ∧ (p5 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159872228757397149628254101552 : ((((((((p5 ∨ True) → p2) ∧ p5) ∧ (p3 ∨ (False ∧ p5))) ∨ ((p1 → p4) ∨ p3)) ∧ p4) → False) → ((p2 ∨ (True → (False ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249072520506320276546517048360 : ((p4 ∨ p1) ∨ ((((True → ((p5 → False) ∧ p3)) ∧ False) → True) → (p1 → (((p2 ∧ ((p3 → (False → False)) → p5)) ∧ (p4 → False)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → (False → False)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643777438473507333624155836477 : ((((p5 ∧ ((((p2 ∧ (p5 ∨ p3)) ∨ ((p1 ∧ True) ∧ True)) ∧ p3) ∧ (((((p3 → p1) → (p1 ∧ p1)) ∧ False) ∧ True) → p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215219695936853671271595298743 : ((False ∧ ((p4 ∧ p2) ∧ p3)) ∨ (p2 → (((p1 ∧ ((p1 → (p4 → True)) ∨ ((p5 → p4) → (True ∨ (p3 ∧ p4))))) → (p3 ∨ True)) ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299123614050448450395907244450 : (False ∨ ((((p2 ∨ (((p5 ∨ p1) ∨ (False ∨ ((p4 ∧ p3) → (((p4 ∨ ((p2 ∧ p2) ∨ p4)) ∨ False) ∨ True)))) ∨ p4)) ∧ False) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42143205432447015989974987630 : ((((p5 ∨ p2) → ((p3 ∨ ((((False ∨ (False → (p3 ∨ (False → False)))) ∨ p2) ∧ ((True ∨ True) → p3)) ∨ p5)) → (p2 ∨ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66593262294342911435878435840 : ((True → (((p5 ∨ False) → ((False ∨ ((((((True ∨ True) ∨ True) ∧ (False → p3)) ∧ p2) → False) ∨ p4)) ∨ False)) ∨ (True ∨ (False ∧ p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199864738201401436860317656569 : (((p5 ∨ (p1 ∧ (True ∧ p2))) ∧ (p1 → p3)) → (p2 → (((p4 ∧ (True → p1)) ∨ (False → True)) → (((p2 → (p1 → p5)) ∨ p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621280720017202686183189404615 : ((((True ∧ (((((p5 → ((p5 ∨ p3) ∨ p1)) ∨ p2) → p4) ∧ (p4 → (p2 ∨ p1))) ∧ (((False ∨ p3) ∨ (p4 ∧ p2)) ∨ p5))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_338356386013551786057817820353 : (p1 → ((((p2 → p2) ∨ True) → p2) ∨ (p1 ∧ ((((False ∧ p5) ∨ ((p2 ∧ True) ∨ p3)) ∨ (p1 ∨ (False ∨ ((False ∨ True) ∧ p4)))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61858052227327969689277237743 : ((p2 ∧ (((p4 → (False ∨ True)) ∧ (((((p5 ∧ ((p3 ∧ p5) ∨ p4)) ∨ p2) ∨ p2) ∨ ((p2 ∧ True) ∨ True)) → (False ∧ p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192445258551528925540401112435 : ((((True ∨ (p2 → ((p5 ∨ p2) ∧ p2))) → p4) ∨ False) → (((p2 ∧ (p4 → ((((False ∨ True) ∨ p5) ∨ p3) → p1))) ∧ p5) ∨ (False → True))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184514303185133622943655136883 : (((p3 ∧ (p2 ∧ ((p5 ∨ (True ∨ p2)) ∧ False))) ∨ (p2 → p5)) ∨ (((p2 ∨ (True ∨ (p3 ∨ p2))) ∨ ((True ∧ True) ∧ (True ∧ False))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_234161976111452335685846913285 : ((True → (p2 → p2)) → (True → ((True ∧ (((p3 ∨ (True ∨ p1)) ∨ p1) → False)) ∨ ((((p3 ∨ (True → False)) ∧ p1) ∨ (True ∨ True)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199693753960674408594047426718 : (((True ∧ ((p3 → p3) → (p4 ∧ True))) → p5) → (p4 → ((((p2 → p1) ∧ ((p4 → ((p4 ∨ (p1 ∧ p5)) ∨ p2)) ∨ p1)) ∧ p1) → p4))) := by
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
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205510796769373937759475788495 : (((p4 ∧ p4) ∧ ((p5 ∧ p5) ∧ p2)) ∨ (((((True → (False ∧ p3)) → (p5 ∧ (p4 ∧ True))) → (p5 → True)) → False) → ((p2 → p1) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (False ∧ p3)) → (p5 ∧ (p4 ∧ True))) → (p5 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134251499083055646419181331631 : ((((p3 ∨ (p2 ∨ True)) ∧ ((((p1 → False) → p2) ∨ (p4 ∧ ((False ∨ p4) → (False → False)))) ∨ (False → False))) ∨ True) ∨ (True ∧ (p4 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306234997729200449448529105210 : (p1 ∨ (((p4 ∨ p2) → p2) → ((p1 → (p3 → p4)) → (p4 → (((((p2 → True) → (p2 → True)) ∧ (p1 ∨ p3)) ∨ (p2 ∨ p3)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53655463926219393539187095321 : ((((p1 ∧ False) ∧ ((True ∨ p4) → ((p4 ∨ p5) ∧ p5))) ∧ (False → (p4 ∧ ((p5 ∧ ((p5 ∧ p3) → ((True → p2) ∨ False))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613223536140089489703951946832 : (((((((((p3 ∧ p3) ∨ (True ∨ p2)) ∨ (p5 → p4)) → (True → p4)) ∧ ((True ∧ p2) ∨ (p1 → (p2 ∨ p2)))) → (p1 ∨ p4)) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p3 ∧ p3) ∨ (True ∨ p2)) ∨ (p5 → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (((p3 ∧ p3) ∨ (True ∨ p2)) ∨ (p5 → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588208141436456245318758847318 : (((((((p1 → (p4 ∧ p2)) ∧ (p1 → (p5 ∨ p4))) ∧ (p2 ∧ (p2 ∨ (p4 ∨ (p4 → (p2 ∨ ((True → p1) ∨ p2))))))) ∨ p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327879870504656288600120512642 : (True → ((p3 ∧ (((p4 ∧ p4) ∧ (p2 ∧ (p2 ∧ p2))) ∨ (((p1 ∨ ((p3 → (True → (p4 ∧ p5))) ∨ p2)) ∨ p2) → p2))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54841822528821273865473789312 : (((p4 → (p5 → ((p3 → p2) ∧ (p4 ∨ True)))) → ((p1 → ((p5 ∨ (p3 → p1)) → (p1 ∧ (p3 → p3)))) ∧ (p2 ∧ (p4 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135239373746733525032085368832 : (((((True ∧ True) → p1) ∨ ((((True ∨ (p2 → p5)) → p5) ∧ ((p5 ∧ p2) ∧ p4)) ∨ (True ∨ p2))) → (False ∧ p3)) ∨ ((p1 ∧ p3) → p1)) := by
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
theorem thm_5_vars_38571109198765739462564977167 : ((((p5 ∧ (((p1 ∨ ((p5 → True) ∨ p4)) ∨ p1) → p3)) ∨ ((p1 ∧ ((p2 ∧ (((p4 → p4) ∨ p3) ∧ False)) → p1)) ∨ False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213939850048678968546538692409 : (((p1 → (p1 ∧ p5)) ∨ p1) ∨ ((p3 ∨ p4) → ((p4 ∨ ((p1 → p3) ∧ ((p1 ∨ p2) ∧ p3))) → (p5 ∨ (p4 ∨ ((p3 → p5) → True)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219895438163843242150480795780 : ((p4 → ((p2 ∨ p3) ∨ p4)) → (((p5 ∧ p3) → ((p1 ∧ p3) ∧ False)) ∨ ((True ∨ ((p4 → ((p5 → True) ∧ (True ∧ p2))) → p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633284187492047490589511258910 : ((((((((p5 ∧ ((p2 ∨ True) ∧ p4)) → ((p3 → p1) ∨ ((p1 ∨ (False ∨ p4)) ∧ (p1 → p3)))) → False) ∧ p4) ∨ (True ∨ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320515131021918058763303129740 : (p4 ∨ (True ∧ ((((p3 → p4) ∧ ((p1 → ((False ∨ p4) ∨ p2)) ∧ False)) ∨ (p2 ∨ ((False → (p1 ∧ p2)) ∨ (p1 ∧ p2)))) ∨ (p5 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54842535549870308573946041765 : (((p5 → (((False → p4) → (True ∨ p5)) ∨ False)) → (((p1 → (((p5 → (p2 ∧ (p3 ∨ p4))) → p2) ∧ p2)) ∨ (True ∧ p5)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797687580531980208674662755851 : (((p1 → ((True ∧ (True ∧ (((((False ∧ p2) ∨ ((p4 ∧ p5) → (False ∧ (p5 ∧ True)))) → p2) → p5) ∧ ((True → False) ∨ p2)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86033866057944049886501858416 : ((((False ∨ p2) → ((p1 → p2) ∨ (p1 ∧ (False → True)))) ∧ (((False → (p4 ∧ p1)) → False) ∧ (((p5 → True) ∧ False) → (False ∧ p1)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p4 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657925721984937146163387569143 : ((((p1 ∧ ((True ∧ ((p5 → p1) → False)) ∧ (p4 ∧ (True → ((p5 ∧ ((p5 ∧ (False ∨ p3)) ∨ p4)) ∧ (p5 ∧ p1)))))) ∨ (p5 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_51140242175857134015493410456 : ((((((((p4 ∧ p5) ∨ ((False ∨ p5) → p2)) → ((p5 → p2) ∧ p5)) ∨ True) → False) → False) ∨ (p3 ∧ ((False ∧ (p3 ∧ p1)) ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ p5) ∨ ((False ∨ p5) → p2)) → ((p5 → p2) ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54267279953342091308830461584 : (((((p3 ∨ p3) ∧ False) ∧ ((p3 ∧ p4) ∧ False)) ∧ (((((p5 → p1) ∧ p2) ∧ (True ∧ (p2 → ((p3 → True) → p5)))) ∨ p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2506927276316889609229555387 : ((p5 → (p1 → ((True ∧ p3) ∨ (True ∧ (p2 → False))))) → (((p1 ∧ (((p4 ∧ p2) → p3) → p1)) ∨ True) ∨ (p5 ∧ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746861306224177475358992875505 : ((((p4 ∨ True) → (((((((p1 ∨ p4) ∨ False) ∧ p4) ∨ p1) ∨ p5) ∧ (p3 ∨ (True ∨ p5))) ∨ (p4 → ((True ∨ (False ∧ p5)) ∨ True)))) ∨ p2) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803308467385909922399312659813 : (((p3 → (((((((True → p1) ∧ True) ∧ p1) ∧ p1) → p1) → ((p4 ∧ (((False ∧ (p3 → p2)) ∨ (True ∧ p3)) ∨ False)) ∧ False)) ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_356451842803677866528849583318 : (p5 → ((p3 ∧ (p2 → ((p1 ∧ ((p2 ∨ p1) ∧ p3)) → (p2 → p2)))) ∨ ((p2 ∨ ((p1 → (p3 ∧ p1)) ∨ p3)) ∨ (p5 → (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323530267978814484621403722228 : (p5 ∨ ((p2 → (p1 ∨ ((((p2 ∨ True) → (False ∨ (p3 ∨ (p1 ∨ (p1 ∧ p3))))) → p4) ∧ (p5 ∧ (p1 ∧ p2))))) ∨ (p3 ∨ (False → p1)))) := by
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
theorem thm_5_vars_723593964455517517228332947999 : (((((p2 ∨ p2) → p2) ∧ (((((p4 → p5) ∧ False) ∨ True) → (((((p4 ∧ (False ∧ p5)) ∧ p3) → True) → (p2 → p5)) ∨ False)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64068147220233073258986068904 : ((False ∨ (((((p1 ∧ p3) ∧ (((p5 → p4) ∨ p5) ∧ p2)) ∨ (p2 ∨ (False ∨ False))) ∨ True) ∨ (False ∨ (p4 → (p5 ∧ (p2 ∨ p5)))))) ∨ p3) := by
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
theorem thm_5_vars_305321310195791889741672241234 : (p1 ∨ ((p4 → (p5 ∧ ((p2 → (((((False → False) ∨ p1) ∧ (False → p1)) ∧ p4) ∧ False)) ∧ False))) ∨ ((((False → p5) ∧ p3) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606841550176730097556085065027 : ((((((((False → True) ∧ (((p4 ∨ (True ∧ ((p4 ∧ p3) ∧ False))) ∧ False) ∧ (p1 ∧ p3))) ∨ p2) ∨ (True ∨ (p5 → True))) ∧ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338634639923262959903676905625 : (p1 → ((True ∧ True) ∧ (p4 → ((True ∧ ((p3 → p4) → p3)) ∨ ((p5 ∧ (((p1 → p3) ∨ p4) ∧ (p1 → p3))) ∨ (False ∨ (True → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42913101918565002811064071274 : (((p3 → (p2 ∨ ((((p4 ∧ ((((p4 ∨ p1) ∧ p2) ∧ True) ∧ p4)) ∧ (p2 ∧ p3)) ∧ (True → (p3 → p1))) ∨ (p2 ∧ False)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752023580038998608668695900161 : (((True ∧ (p5 ∨ (p5 → (True → ((((p2 ∨ (p4 → (False ∧ p4))) → p5) ∨ ((p3 ∧ True) ∨ p3)) → (p5 ∧ ((True → p4) → p4))))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h11 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h19 := h10 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h22 := h10 h21
      -- One of the premise coincides with the conclusion.
      exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983146585640815271213544959687 : (((p1 ∧ (((p4 ∨ ((False → ((False ∨ False) ∨ p2)) → ((p1 → p4) ∧ p4))) → (p5 → p1)) → (p1 ∧ ((p4 → (p5 ∨ p2)) ∧ False)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ ((False → ((False ∨ False) ∨ p2)) → ((p1 → p4) ∧ p4))) → (p5 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133968225154962501926280884642 : (((p5 → (((p3 ∧ True) → (p5 ∧ (((p3 ∨ False) ∧ (True ∧ (p5 ∧ p1))) → ((False ∨ p3) → p3)))) → p1)) ∧ p5) ∨ (p2 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219819327897467477150123622526 : ((p3 → ((p4 ∨ p3) ∧ p3)) → (((p1 ∨ (p2 → True)) → (p4 ∧ False)) ∨ ((((p4 ∧ ((p3 ∧ True) ∨ p2)) ∧ True) → p4) ∧ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737329922085694011107291244763 : ((((p4 → p2) ∧ ((False ∨ (((((p2 ∨ (p2 ∨ (p3 → p2))) → p5) → ((p1 ∨ p5) ∨ p4)) → (p2 → p5)) ∧ p3)) ∧ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141925499784070234372576452127 : (((p1 ∧ p2) → (True ∨ ((True ∨ p1) ∧ (True → ((((True ∧ ((p2 → p5) → p3)) ∧ True) ∨ p4) ∧ (p3 ∨ False)))))) → (p5 → (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161517855333537477762398144715 : ((p4 ∧ (p5 ∧ (p3 ∧ (True → (True ∧ ((p3 ∧ False) ∧ (((p1 → p3) ∨ (p1 → True)) → p1))))))) → (((True → p4) ∨ p5) → (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h35, we can now drive its conclusion.
    let h37 := h35 h36
    -- We need to get the right conjuct of h37 based on <expert-advice>.
    let h38 := h37.right
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- We need to get the right conjuct of h39 based on <expert-advice>.
    let h40 := h39.right
    -- False on the left can always be used.
    apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309650298078596911309098025388 : (p2 ∨ ((p4 ∧ ((p3 ∨ p2) ∨ (p3 ∧ ((False → (p1 ∧ ((((p2 → p3) ∧ p4) → False) ∧ True))) ∨ (p3 ∧ False))))) ∨ ((False ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173421158551514180401834513610 : ((p5 → (((True ∨ p3) ∨ p2) ∧ ((p3 ∨ ((True → p1) → p4)) → (False ∨ False)))) ∨ ((False ∨ ((p2 → (p5 ∧ p1)) ∨ (True ∨ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_107076072395899104475345275012 : ((((p1 ∨ p4) ∧ (True ∧ p5)) → (((p3 ∨ (p2 ∨ p2)) → ((False ∧ (False ∨ (p1 ∧ False))) ∨ ((False → p5) ∨ p4))) ∧ True)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h16.left
        let h23 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h26.left
        let h33 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708651770175785192378511998962 : (((((((False ∧ (p1 ∧ False)) → p3) ∧ False) → p4) → ((p4 → (False ∨ ((p2 ∨ (True → (p4 ∧ p1))) ∧ (False ∨ True)))) → (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51985815383468293304594204166 : ((((p4 ∨ False) ∨ (((p5 ∧ ((p5 ∧ p1) ∨ (p1 ∨ (p3 → True)))) ∨ p2) → False)) ∨ ((p1 ∧ False) → (((p2 ∧ p1) → p3) ∧ True))) ∨ p4) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663915615054811032653199854233 : ((((p4 ∧ (((((p5 ∧ p4) → False) → (((False → p4) ∨ (((p1 ∧ p5) ∧ True) ∧ p4)) ∧ (p1 → p5))) ∨ True) → p1)) → (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50567669086597400725254080345 : ((((((True ∨ p1) → (p1 ∨ ((((False ∧ p1) ∧ p5) ∧ False) → (False → p2)))) ∧ (p5 → p2)) → p3) → (p4 ∨ ((p3 → p1) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47368400570489249595945616135 : ((((p1 → p2) ∨ ((((p3 ∨ True) → (((((p5 ∧ p3) ∧ p3) ∧ (True ∧ p5)) → p2) → (p5 ∨ p2))) ∧ p4) ∨ True)) ∨ (p2 ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152801964772818533657651885513 : (((True ∨ False) → (p1 ∧ ((((p5 → (p2 ∧ (p1 ∧ False))) ∨ (p1 ∨ p2)) ∨ (p3 ∧ p1)) → (p3 ∧ p4)))) → (p3 ∨ ((p2 → p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 → (p2 ∧ (p1 ∧ False))) ∨ (p1 ∨ p2)) ∨ (p3 ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47085741242385764223372099220 : ((((((p5 ∨ (p2 ∨ True)) ∨ ((p3 ∧ p3) → p3)) ∨ (p3 ∧ (p5 → (p2 → (p2 → (p4 → p4)))))) → (True ∧ False)) ∨ (True ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824577594740426801421431373397 : (((((True → (p1 ∧ False)) ∧ (((((True ∨ False) ∨ p1) ∧ (p3 ∨ p1)) ∧ (p4 ∨ ((p4 → p2) → (p2 ∨ (p4 ∧ p5))))) ∧ p3)) ∧ p3) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h18 := h4 h17
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h24 := h4 h23
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h31
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h38 := h4 h37
        -- We need to get the right conjuct of h38 based on <expert-advice>.
        let h39 := h38.right
        -- False on the left can always be used.
        apply False.elim h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689986786868343526112802095019 : ((((p1 ∧ ((((p3 ∧ p2) ∨ True) → p1) ∨ ((p2 → (False ∧ p5)) ∧ (p4 ∨ p2)))) ∨ (False → ((p5 → p3) ∧ (p2 → (p2 ∨ False))))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561879248049394785105992766468 : (((p5 ∨ (((p4 ∧ (((((p5 → (p3 → p2)) ∨ (False → p4)) ∧ p2) → p1) ∨ False)) ∨ (((p5 ∧ (True → False)) ∧ p1) → p3)) ∨ p1)) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124292853025199489041336905660 : ((((((p5 → True) ∨ (p2 ∧ p3)) → True) → False) ∧ (((p5 → (p5 ∨ p2)) → ((p1 ∧ False) ∧ False)) → ((p3 ∨ p3) → p5))) → (p5 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 → True) ∨ (p2 ∧ p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (((p5 → True) ∨ (p2 ∧ p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622357041901826112708195638297 : ((((p3 ∧ (((((p2 ∧ (p1 ∨ p1)) → p3) → p5) → (p5 → (True → (((p5 → (p5 → p2)) ∨ p2) ∧ p3)))) → (p5 → p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_148347802013101680808018436887 : ((((p1 ∨ (p3 → False)) ∨ ((p2 ∧ (p5 ∨ ((False → False) → p4))) ∧ True)) ∧ (p4 → (p2 → (p5 ∨ p4)))) ∨ ((p1 ∨ (p5 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148567293680094605553204029886 : (((p3 ∧ ((False ∨ (p2 ∨ (False → p5))) → (p3 ∧ p4))) ∧ ((p3 → p5) ∨ ((p3 ∧ p2) → (p4 → p2)))) ∨ (True ∧ (p2 → (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193823929205565279690007387908 : ((p5 ∧ ((p3 ∧ False) → (p3 → (p5 ∨ (False ∨ p5))))) → ((p3 ∨ (((True ∧ (((p1 ∧ True) → True) ∨ p5)) → p3) ∧ (False ∨ p4))) → p3)) := by
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
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h13 : (True ∧ (((p1 ∧ True) → True) ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h13
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165945443977468526411588990482 : (((p2 ∨ True) ∧ (p4 → (((p3 ∨ ((p5 ∨ p2) ∧ p1)) ∨ True) ∨ (p5 ∧ (p1 ∨ p3))))) ∨ (True → (((p4 → p4) ∧ p2) ∧ (True ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148809365294217266671513470088 : ((((True → (p3 → p1)) ∧ (True ∨ p3)) → (p1 ∨ (((p4 → p5) ∧ ((p4 → p2) ∧ p3)) ∨ (False → p4)))) ∨ ((p2 ∨ (p1 ∧ p2)) ∧ False)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262279032488921474835938295628 : (True ∧ (((p5 ∧ (((((p1 → p3) ∨ False) → p3) ∧ p1) ∧ ((p3 ∧ p2) → ((p1 ∨ False) → p1)))) → ((p3 ∧ p3) ∨ (p4 ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340839915873682215434044042781 : (p2 → ((((((((p4 ∨ p2) → p4) ∨ (p5 → p1)) → ((p3 ∨ True) → p5)) ∧ (False ∨ (p2 ∧ p2))) ∧ p5) ∧ ((p1 → p2) → p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347185688253370953328885178766 : (p3 → (((p4 ∧ (p4 ∨ (p2 ∧ ((p3 ∧ (p2 ∨ p3)) ∧ p1)))) ∧ True) ∨ (p5 ∨ ((p2 → ((p1 ∧ False) → p2)) ∨ (p5 ∨ (True ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749210467482036874664832028246 : ((((p5 → p3) → ((((((p4 ∨ p5) ∧ (p4 ∨ (p2 → p3))) → p3) ∧ (((p1 ∨ p5) ∨ p2) → True)) → (p3 ∧ (p3 ∨ True))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_178813290319607755731084391039 : (((p3 ∧ (p5 ∨ p3)) ∨ ((False ∨ (False ∨ p4)) ∨ (p3 ∧ (True → False)))) ∨ ((p3 ∨ ((p4 → p3) → p5)) → ((False ∧ (p5 → p4)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_696489191555394654553046413776 : ((((((p5 → p3) ∧ ((p3 ∧ (p4 ∨ (p3 → False))) ∨ p4)) ∧ False) ∧ ((((p3 ∨ p4) ∧ (p2 → p1)) ∧ ((p4 → p3) ∧ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39161287267274078403700302344 : ((((p3 ∨ p4) → ((p5 ∧ (p1 ∧ False)) ∨ ((p2 ∨ (p2 ∧ (((p5 → (False → False)) → (p5 ∨ (p5 → p4))) ∧ p2))) ∧ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116347338278064343682264281468 : ((((True ∨ True) ∨ p4) → ((p1 ∧ (False → (p5 ∨ (((p2 → (p5 → p2)) ∧ p3) ∧ (p2 ∧ (p2 ∧ p3)))))) → (p1 ∧ p5))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647708875287760822782893457405 : ((((p5 → (p1 ∧ (p4 ∧ ((p1 ∨ (p4 → ((True ∧ ((p2 → (p2 ∨ p1)) ∨ (False ∧ (p3 ∧ (False ∧ True))))) ∨ False))) → p2)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122916166103178019649250022990 : (((True → ((p2 ∨ ((p1 → p4) ∨ (((((p1 ∧ p4) ∧ p5) → p2) → p2) ∧ False))) ∧ (p5 → p1))) ∧ (p1 → (p3 ∧ p4))) → (p4 ∨ True)) := by
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
theorem thm_5_vars_321646935023555657758869056640 : (p4 ∨ (p3 → (p2 → ((p5 ∨ (False ∨ (((((p3 ∧ p2) ∨ p5) → p3) ∧ True) → (False ∧ p3)))) ∨ ((p3 ∧ ((p4 ∧ p5) ∨ True)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231102393798833426771506229180 : (((False ∨ p4) ∨ p2) → (((False → p2) → (((True ∨ p5) ∧ p4) ∧ ((p5 ∧ (p2 ∧ p1)) ∨ ((((p1 ∧ p3) ∧ True) → p3) ∨ p2)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225487588776909432083490380142 : (((p5 ∨ True) ∧ p5) ∨ ((True ∧ ((p4 ∧ p1) ∧ ((p3 ∧ (p2 ∨ True)) → p1))) → (((p3 → p2) ∧ (p1 ∨ True)) ∨ (True ∧ (p1 ∨ p1))))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193110549396622798491906138013 : (((p5 → (False ∨ (p2 ∧ p1))) ∧ ((p4 → False) ∨ p1)) → ((p4 ∧ (((False ∧ False) ∨ True) → ((False ∧ ((p1 ∨ p1) ∨ p2)) ∨ False))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : ((False ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



