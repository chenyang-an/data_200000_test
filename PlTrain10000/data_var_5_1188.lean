variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351623125353889844575852671139 : (p4 → ((((p4 ∧ (p5 → (p4 → (p3 ∧ (p1 → ((True ∨ False) ∨ False)))))) → False) ∧ True) ∨ ((False ∧ (p4 ∧ ((p3 ∧ p4) ∨ p4))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786684732975025834918574913832 : (((p4 ∨ ((((p2 ∨ p2) ∨ False) ∧ (True ∧ p1)) ∨ (((p3 ∨ p4) ∧ True) → (True → ((((p2 → (p5 ∨ p3)) ∨ p3) ∧ p2) → p2))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705963897640351735976719492938 : (((((p5 ∧ (p3 ∨ p2)) → (p3 ∧ (p2 ∧ p3))) ∧ ((((p4 ∧ p1) ∨ p1) ∨ p1) ∨ ((p1 ∧ (True → ((False ∧ False) ∧ p2))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55782343695217863569032069911 : ((((p5 → p1) ∧ (p5 ∨ True)) ∧ (False ∨ (((p4 ∨ p2) → False) ∧ (True → (((p3 ∧ (((p4 ∨ p5) ∨ p5) → p5)) ∨ p1) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64342883409139266364283477186 : ((p1 ∨ ((p1 → ((True ∧ (p1 → (((((((p2 ∧ True) → p2) → p3) ∨ False) ∨ p4) ∨ (p2 ∨ False)) → p1))) → (p4 ∨ p5))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314649063993374202382174880013 : (p3 ∨ (((p1 ∧ (True ∨ ((p1 → ((True ∨ p3) → (p4 ∧ True))) ∧ False))) ∨ (p3 ∧ p1)) ∨ (((True ∧ (p3 ∨ p4)) ∨ p2) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_689992148291998746799684932405 : ((((p1 ∧ (p3 ∧ (((True ∧ False) ∧ ((p1 ∨ p3) ∨ (p3 → True))) ∧ (p4 ∨ True)))) ∨ (((p3 → p2) ∨ p1) ∨ (False → (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179235800510656268832440668262 : ((p5 ∧ ((p3 ∧ (False ∧ ((p1 → p2) → (p1 ∨ (p3 ∨ True))))) ∧ p2)) ∨ (False → (p5 → ((((p3 ∧ False) → p1) ∧ (p3 ∧ p1)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204451951540228414758409130743 : ((((False ∧ (p2 ∨ False)) ∧ p2) ∨ False) ∨ (False → (p3 ∧ (((((p5 → (((True ∧ True) ∧ p1) → p3)) ∧ p2) ∧ False) → (False ∨ False)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
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
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260568973394693666434517009957 : ((p3 → p1) → (p1 ∨ ((((True ∧ (p2 ∧ p2)) → p4) → (p4 ∨ ((p2 → ((True ∨ ((p2 ∧ True) ∨ p2)) ∨ p3)) ∨ (p1 ∧ True)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178198842003207334703307641974 : (((True ∨ ((p4 → p1) ∨ (p5 ∨ (False → (p2 ∨ (p4 ∧ p4)))))) → False) ∨ ((((p5 ∧ p5) ∧ False) ∧ ((p4 ∧ p2) ∨ (p3 ∨ p5))) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105161481304023302537164098110 : ((((p1 ∨ p5) ∨ (p1 ∨ ((((p1 → (False ∧ p3)) ∧ p4) ∧ (False ∨ ((p2 ∧ p4) → p5))) ∨ True))) ∨ (False → (False ∨ p3))) ∧ (p2 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555115011046763548172907272556 : (((p2 ∨ (p2 ∨ (((p5 ∧ (p3 ∨ (p4 ∨ p1))) → (p2 ∨ True)) ∨ ((p1 ∨ ((p3 → p1) → (p5 → (p1 ∨ p2)))) ∧ (p2 ∧ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673308356659389176697920644521 : ((((((True ∧ True) ∧ ((p3 → p1) → (p5 ∨ False))) → ((p3 ∨ p3) → (True ∨ ((p3 ∧ p2) ∨ (True ∧ p4))))) → ((p1 ∧ True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753426765291786246371092479510 : (((False ∧ (((p2 ∨ (p1 → True)) ∧ (((p1 ∧ ((p3 ∧ p2) ∨ ((False ∧ p2) ∨ p1))) → p2) → (p4 → p2))) ∨ ((p1 ∨ False) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153279659901081058859212383495 : ((False ∨ (True → (p1 ∧ (((((p1 ∧ (p4 → False)) ∧ True) ∧ p1) → ((p4 ∧ p4) → (True ∨ False))) → p5)))) → ((p3 ∧ (p1 → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((((p1 ∧ (p4 → False)) ∧ True) ∧ p1) → ((p4 ∧ p4) → (True ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h18 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119439256664842852576859104771 : ((p4 → (((p3 → False) ∨ ((p2 ∨ p4) ∨ (p2 → ((p3 ∨ p4) ∨ (p2 ∨ p1))))) ∧ (p5 ∨ ((p4 ∨ p1) → (p3 ∨ p4))))) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58731453352779367472573198637 : (((p3 → p3) ∧ ((((p4 → (p5 → ((p3 → (p3 ∧ p5)) ∨ p3))) → p4) ∨ ((p3 → False) → (True → (False → (p1 ∨ False))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135973975166446093570537164641 : ((((p5 ∨ (((p4 ∨ p1) ∨ (p1 ∨ p1)) ∨ p4)) ∧ p2) ∨ (((p4 ∨ ((False → p4) ∧ p2)) → p3) ∨ (True ∨ p4))) ∨ (True ∧ (p1 ∨ False))) := by
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
theorem thm_5_vars_60705794636097765841920006389 : ((True ∧ (((((p1 → p4) → p4) ∧ False) ∧ (p3 ∨ p3)) ∨ ((False ∧ (((p3 → (p2 → p1)) ∨ p2) ∧ ((p2 ∧ p5) ∨ False))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53785051059219462871062985885 : ((((p3 ∨ (p4 ∧ (((p4 → p1) ∧ p1) ∨ p3))) ∨ p4) ∨ (p3 → ((p5 ∧ (True ∧ (True → (False ∨ False)))) → ((p2 → False) → p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170405622090353025021684910245 : ((((p3 ∨ p2) ∨ False) ∨ (((p5 ∨ p5) ∨ (((False ∧ p2) ∨ p4) → True)) ∨ p3)) ∧ (((p2 ∧ (((p2 ∨ p1) → False) ∨ False)) ∨ True) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719126847028427674317447630818 : ((((p1 ∧ ((False ∧ p4) ∧ p5)) ∨ (p2 → (p1 ∨ (((((p5 ∧ (p3 ∧ p5)) ∨ (p4 ∧ p4)) ∨ p2) ∧ (p3 ∨ (p1 ∨ p3))) ∨ p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_265042290261770448303064193212 : (True ∧ (True ∧ ((((p5 → p2) ∨ (p5 → (p4 ∧ (False ∧ p3)))) → ((p3 ∧ ((p3 ∨ (p3 ∧ False)) ∧ False)) ∧ True)) ∨ (p3 → (True → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166446818773911317884036428375 : ((p2 ∨ (((p2 → p1) → (((False ∧ False) ∧ True) ∨ (p5 ∧ (p3 → (p1 ∧ p3))))) → p3)) ∨ (((True ∨ True) ∧ ((p4 ∧ True) → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41316491313927313501994532474 : (((((((p1 → (p3 → p1)) → p3) ∨ p1) ∨ (p5 ∧ (p5 ∨ ((p4 ∧ p2) → True)))) ∧ ((p3 ∨ False) → ((p2 → p5) → p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712702171779921365868385730345 : (((((p2 → p3) ∧ (True ∧ (False ∧ False))) ∨ ((True ∧ ((((p1 ∧ p4) ∨ p1) ∨ p5) ∨ ((p2 ∨ False) ∨ (p1 ∧ (False ∨ True))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53973524401765450884954031732 : ((((p5 ∨ (True ∨ (p3 ∧ ((True ∧ p4) ∧ True)))) ∧ p3) → ((((False ∧ False) ∨ True) ∨ p5) ∨ ((p1 ∧ False) → ((p5 ∨ True) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148277557578003089823014963236 : (((((p5 ∨ (p3 → ((True → ((p4 → p5) → p4)) ∨ True))) ∧ (p1 ∨ p5)) ∨ p3) → (p4 ∨ (True ∨ p3))) ∨ ((p5 → (True ∨ p5)) → p1)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114070956127414571375474119944 : ((((((p5 ∨ (p1 ∨ False)) ∨ True) ∧ p5) → ((False ∨ p2) ∨ ((False ∧ (p5 ∧ (False ∨ p4))) ∧ p4))) ∨ ((p5 ∨ True) ∨ p1)) ∨ (p1 ∨ p4)) := by
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
theorem thm_5_vars_111306632166093226873982998523 : (((False ∧ ((p1 ∧ (p3 ∧ (True ∨ (p5 ∨ ((((p5 → False) ∨ False) → p5) ∧ False))))) ∧ (p3 ∨ ((False ∧ p4) ∨ True)))) ∧ True) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45111987527474705292311544289 : ((((p3 ∨ p3) → ((p4 ∧ ((False → (p1 ∧ (True ∧ p3))) ∧ (p2 → (False ∧ (((p3 → p1) ∨ True) ∨ (p2 ∨ p5)))))) ∧ True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493066654365361890423894371969 : ((((p4 ∨ (p3 ∨ (p1 ∨ p3))) ∨ (p4 → ((((((((p5 ∧ p3) ∨ p3) ∧ p2) → (True ∨ (p4 → p4))) ∨ False) → False) ∨ p4) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138155807590125463915729381282 : ((p1 → (((p3 → p5) → (((((False → p5) ∨ p5) → (True → ((p1 ∧ (p3 ∧ p4)) ∧ p1))) ∨ p2) → False)) → p5)) ∨ (p4 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350005862098956363571129472911 : (p4 → (((p5 ∧ (True ∧ ((((False ∧ ((False ∨ ((p4 ∨ p4) ∨ p3)) ∧ (p5 ∨ p5))) ∧ p4) ∨ ((p3 ∧ False) ∨ p3)) ∧ p2))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8278944752369699494868214650 : (((((((p4 → p3) ∨ False) → (p3 → (p1 ∧ (((False ∨ p2) ∨ p4) ∧ (p3 → ((False ∧ False) ∧ (p1 ∧ True))))))) → p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41259669233982770511661941495 : ((((((False ∧ False) ∨ p3) ∧ (((p2 → ((p2 ∧ p1) ∧ (p2 ∧ p5))) ∨ (p1 ∧ p3)) ∨ p5)) ∨ (((p4 → True) ∧ p4) ∧ p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65230361001552405299209045911 : ((p3 ∨ ((p4 ∨ (((p1 ∧ p5) → ((p3 ∧ (p3 ∨ p5)) → ((p1 → (True → ((p1 → True) ∧ True))) ∧ False))) → (p3 ∨ p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51233899555612809256558319507 : ((((False ∨ (p3 ∨ (False ∨ False))) → (((p5 ∨ (p1 ∧ p4)) → (p4 ∧ (p2 → p2))) → p2)) ∨ (p2 ∧ ((True ∨ (p1 → p5)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682585311461191359614527580474 : (((((((p3 ∧ p3) → p2) ∨ ((p1 ∧ p1) ∧ p1)) ∧ (p4 → ((p1 → (True ∨ p5)) ∧ False))) ∧ ((p3 ∧ ((p3 → p5) ∧ p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322328742177294652539607951496 : (p5 ∨ (((((p1 → (False ∨ (p4 ∨ p3))) → (p1 ∨ ((p2 ∨ (p5 ∧ ((p2 ∧ p5) ∨ p1))) ∧ p2))) ∧ (False ∨ False)) ∨ (False ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135018506393910936158800368304 : (((True → (p1 ∨ ((False ∧ ((False ∨ False) → (p5 ∨ (p5 → p3)))) ∨ ((p2 ∧ (p4 ∨ p4)) → p1)))) ∧ (p1 ∨ p2)) ∨ (True ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257197450916836500980823385027 : ((p2 ∨ p2) → ((p3 ∨ (((p2 ∨ p4) ∨ p2) ∧ (True → ((p3 → (p3 ∧ (p4 ∧ p3))) → ((p3 ∨ False) ∧ (p1 → p5)))))) ∨ (True ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664175078572295120441968581868 : ((((False ∨ ((p1 → (p5 ∧ (False ∨ True))) ∧ (p4 ∧ ((False ∧ False) → (((p4 → p5) ∨ p3) ∧ (p2 → (False → p1))))))) → (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353657272384413881329065711110 : (p4 → (p5 ∨ ((p3 ∨ (((False ∨ p2) ∨ (True ∨ (p1 ∧ False))) ∧ (((((p1 ∧ True) ∧ True) → ((p4 → False) ∨ False)) ∧ p4) ∨ p2))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120126798318998486946902172028 : ((((p2 → (p2 ∧ p3)) ∧ (((((p3 → ((True ∧ False) ∨ p4)) ∨ p5) ∧ ((False ∨ (False → p1)) → p2)) ∨ p5) ∧ p2)) ∧ p3) → (p1 → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49811015023665867204626133972 : (((p1 → ((p1 ∨ ((p4 → ((((p5 ∧ p4) ∨ ((p1 → p1) ∧ p3)) → p5) → (p4 ∨ True))) ∧ p3)) ∧ p1)) → (p5 ∧ (p1 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117474211292691118781964040896 : ((p1 ∧ (p5 ∧ ((False ∧ ((((p4 ∨ (p4 ∧ True)) → False) → (((p1 ∧ (True ∨ False)) ∧ p4) ∨ True)) → (p2 ∧ p3))) ∨ False))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146938790789833617985769373577 : (((((((p1 ∨ p1) ∧ (p3 ∧ (((p3 ∨ (p1 ∨ False)) → (p1 ∨ p3)) ∧ False))) → True) → p1) ∨ p2) ∧ p3) ∨ ((p5 → (p4 ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140337438920035071038378284186 : (((((p2 ∨ p4) ∨ (True → (p4 ∧ ((p1 → ((p1 ∨ (p4 ∧ False)) → True)) → p2)))) ∨ p3) ∨ ((p3 → p1) → p3)) → (p1 ∨ (True ∨ p4))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h6 =>
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676483026234512744119873778344 : (((((p3 → p2) → (p4 ∨ (p4 ∧ (((True ∧ (p5 ∨ (False ∧ p4))) ∨ p3) ∧ ((p3 → p2) ∧ p2))))) ∧ (p1 ∨ (p3 → (p2 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158763032773667910313652435580 : ((p4 ∧ (((p3 → p1) → p4) ∨ (((False ∨ p4) ∨ (True → ((p2 ∨ (p4 ∨ p2)) ∧ p2))) → p4))) ∨ (p4 ∨ ((False → (p1 ∨ False)) ∨ False))) := by
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
theorem thm_5_vars_114593338091153090932303806419 : ((((True → p4) ∨ (((p5 ∧ ((p4 ∨ p1) → p5)) → p3) → ((True ∧ False) ∨ p1))) ∧ ((False ∧ ((p2 ∨ p2) → False)) ∧ p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669906622757498349294042099583 : (((((p2 → (((p2 ∧ ((True ∨ p5) ∧ (p1 → p4))) → p5) ∨ p1)) → (((p3 ∨ p5) ∨ p1) ∧ (p4 → False))) ∨ ((False ∧ p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115134010691419915903534325966 : ((((True ∧ p5) ∧ (((p1 ∨ False) ∧ ((p1 → True) ∧ True)) → p3)) → ((p5 ∧ p4) ∨ (p1 ∨ ((False ∨ p3) ∨ (False ∨ True))))) ∨ (p5 → p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741381025459381158388940686227 : ((((p5 ∨ False) ∨ (((((p1 ∨ (True ∨ p3)) → (p3 → False)) ∨ (p2 ∧ ((True → (p5 ∧ False)) → False))) ∧ ((p2 ∧ p3) ∨ p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182434308158439783280466419256 : (((((False ∨ (p2 ∨ (p2 ∨ False))) → p5) → False) ∨ (True ∨ p3)) ∧ ((p1 ∧ (False → p3)) → (((p2 → (p1 ∧ p5)) → p3) → (p4 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193241273594833906184448695974 : ((((p1 ∨ p4) → False) ∧ (((True → p4) ∨ p1) ∨ p1)) → ((((True → p3) ∧ p5) → (False ∧ p5)) ∧ ((True ∧ (False → (True ∨ p5))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h26 =>
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Implications on the right can always be decomposed.
  intro h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h35 := h33 h34
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h36 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h37 : (p1 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h38 := h30 h37
      -- False on the left can always be used.
      apply False.elim h38
  case inr h39 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h40 : (p1 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h41 := h30 h40
    -- False on the left can always be used.
    apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717450400388137000474622286687 : ((((p1 → ((False ∨ p4) ∧ False)) ∧ (p5 ∨ (p1 ∨ (True ∧ (((p4 → False) → ((p2 → p2) ∨ (False ∧ ((p5 ∨ p3) → p3)))) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44855239503326973824048121407 : ((((p4 ∧ (p5 ∧ p2)) ∨ (((((False ∧ ((p3 ∨ p3) ∨ p1)) → ((p3 ∧ True) ∧ p3)) → True) ∧ ((p4 ∧ p2) → False)) ∧ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150232110692171538734550590131 : ((p2 → (p5 → ((((p3 ∧ (p2 → p5)) → p1) → True) → (((False → p2) → ((p1 → p2) → False)) ∨ p5)))) ∨ (p5 ∧ (p4 → (p4 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172383934586549299807235549526 : ((((p1 ∨ (p1 ∨ (True → p4))) ∨ p2) → (((p2 ∨ p4) ∧ (p2 ∧ p2)) ∧ p3)) ∨ (p5 ∨ ((p2 → (p1 → (p4 → p1))) ∨ (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61109472651282315003514832957 : ((False ∧ ((((p2 → False) → ((False → False) ∧ ((p4 ∧ p3) ∨ p2))) → False) ∧ ((p5 → ((p5 ∧ ((p4 ∧ True) ∧ True)) ∨ p4)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937056682479461461323454046894 : (((((p3 → (p4 → (p5 ∨ True))) → p3) ∧ (p1 → (True ∧ (p5 ∧ ((p5 ∨ ((p3 ∨ (((False ∨ True) ∨ p4) → p2)) ∧ p1)) ∧ True))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (p4 → (p5 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442255202481784541838511499907 : (((((((p2 ∧ (((p1 ∨ True) ∨ (p1 → (p5 → (True ∨ False)))) ∨ (p1 ∧ True))) ∧ p3) → (p4 ∧ p5)) ∨ True) ∨ (p5 ∧ (p4 ∨ p4))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_233669615564033428025109154661 : ((p2 ∨ (p5 ∨ p5)) → (p5 → ((((((p1 ∧ (p1 ∨ False)) ∧ p3) ∨ p4) ∨ p2) ∧ p5) → (True ∧ ((((p5 ∨ p3) ∨ False) → False) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339159947508220747376962311642 : (p1 → (p1 ∧ (False ∨ (((((p5 ∧ p3) ∨ (True ∨ p4)) ∧ (p1 ∧ (p1 → ((p5 ∧ p2) ∧ (p4 ∧ ((p5 ∨ p1) ∨ p5)))))) → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h4.left
      let h17 := h4.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h4.left
      let h24 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187154522477144189255056071724 : (((p2 → False) ∨ (p1 ∧ ((p3 ∨ (p1 ∨ False)) ∧ (p5 → p2)))) → (((((p4 ∧ (p3 ∨ ((p2 → p1) → p5))) → p3) ∧ True) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713350956170719103938224960527 : ((((True → (p1 ∨ (p1 ∧ (False ∨ True)))) ∨ (p5 → ((False → (p3 → p5)) → ((p2 ∨ ((p2 ∨ True) → p1)) → (p5 ∧ (True ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51755173012079295137923815495 : ((((False ∧ p1) ∨ (p1 ∧ (p2 ∨ ((((p1 ∧ p3) ∧ (p2 ∧ p2)) ∧ p3) ∨ True)))) ∧ (((p2 ∧ p4) ∧ True) ∧ ((p3 ∧ p3) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55031452344042181145968557875 : (((p2 ∧ (p5 → (p4 → (p1 ∨ p3)))) ∧ ((((((True → (p5 ∨ p5)) ∨ p2) ∧ p5) ∨ True) ∨ ((p3 ∧ p1) ∨ (True → True))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661306632596926905625885287852 : (((((((p3 ∨ (p5 ∧ (p5 ∧ (((p5 ∧ p5) ∨ p2) ∧ ((p5 → True) → (True ∧ p1)))))) → p1) → p3) → (p2 ∨ False)) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232486668713730856535214563680 : ((True ∧ (p5 ∨ p3)) → ((p5 → ((p5 ∨ (((True ∨ ((p2 ∧ p1) ∨ p1)) ∨ (p3 → (p1 → p3))) → True)) → False)) ∨ (p5 ∨ (True → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40625631164036380926415894930 : ((((((((False → p5) ∧ p1) ∨ (((((p4 ∨ False) ∧ (p2 ∧ (p1 ∧ p5))) ∨ (p3 ∨ p5)) → False) ∨ p4)) ∧ p2) → False) → p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777437939293424939009280810940 : (((p1 ∨ ((p5 → (p2 ∨ ((((p1 → (p5 → p4)) ∧ True) → p3) → (p3 → (p5 ∧ p1))))) ∨ ((True ∧ (p5 ∧ (False → p3))) → True))) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134194035809416074693750732422 : ((((((p3 ∨ False) ∧ p1) ∧ (((p2 ∧ p1) ∨ True) → p2)) ∧ (((False → True) → (p2 ∧ p3)) → (p2 ∧ True))) ∨ True) ∨ (p4 ∨ (p3 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231965135172311156448434051491 : (((p1 ∨ p3) → p5) → (((p5 ∨ (p4 ∨ False)) → ((p1 ∨ p1) ∨ ((p1 → ((p1 ∧ (p4 ∨ True)) → p3)) → ((True → False) ∨ True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225741290408971863944437025992 : (((p4 → p3) ∧ True) ∨ ((p5 → ((p5 ∧ (((p4 ∧ (p2 → p4)) ∧ ((True ∧ p2) ∧ (True ∧ p4))) ∧ p4)) ∧ (p2 → p5))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261602163576565443814356054688 : ((p5 → p4) → (p2 ∨ ((((((p1 ∧ p2) ∨ (p2 → p2)) → ((p5 → ((p1 ∨ p2) ∨ p3)) → True)) ∨ (p2 ∧ p4)) → (p4 → p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261523145463216200589966661767 : ((p5 → p3) → (((True → ((p2 ∧ p1) ∨ True)) → False) ∨ ((True ∨ p4) ∨ ((((p4 ∨ (True → (True → (p2 ∧ p4)))) ∨ p2) ∧ p4) ∨ p3)))) := by
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
theorem thm_5_vars_89135650754926048431570556917 : ((((p1 ∧ p1) → False) ∧ ((((p2 → True) ∧ p1) ∧ p4) ∧ ((p4 ∧ ((p3 ∧ True) → (p2 ∨ (True → (p5 → p1))))) ∧ (p1 → p3)))) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h14 : (p1 ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96872781915136447246584385011 : ((p1 ∨ (((p4 ∨ p2) ∨ (((False ∧ (p4 → True)) ∧ p1) → (p3 → p3))) ∧ (((p2 → (p3 → p2)) → p1) ∧ (p4 ∧ (p3 ∨ p3))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h13 : (p2 → (p3 → p2)) := by
            -- Implications on the right can always be decomposed.
            intro h14
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h16 := h8 h13
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h18 : (p2 → (p3 → p2)) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- Implications on the right can always be decomposed.
            intro h20
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h21 := h8 h18
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h5.left
        let h24 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h28 : (p2 → (p3 → p2)) := by
            -- Implications on the right can always be decomposed.
            intro h29
            -- Implications on the right can always be decomposed.
            intro h30
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h31 := h23 h28
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h33 : (p2 → (p3 → p2)) := by
            -- Implications on the right can always be decomposed.
            intro h34
            -- Implications on the right can always be decomposed.
            intro h35
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h36 := h23 h33
          -- One of the premise coincides with the conclusion.
          exact h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h5.left
      let h39 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h43 : (p2 → (p3 → p2)) := by
          -- Implications on the right can always be decomposed.
          intro h44
          -- Implications on the right can always be decomposed.
          intro h45
          -- One of the premise coincides with the conclusion.
          exact h44
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h46 := h38 h43
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h47 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h48 : (p2 → (p3 → p2)) := by
          -- Implications on the right can always be decomposed.
          intro h49
          -- Implications on the right can always be decomposed.
          intro h50
          -- One of the premise coincides with the conclusion.
          exact h49
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h51 := h38 h48
        -- One of the premise coincides with the conclusion.
        exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588662200204467340085811260710 : (((((p1 ∧ (((p3 ∧ p4) ∨ (((p1 ∧ (False ∧ ((((p4 ∧ p3) → p5) ∧ p1) ∧ True))) ∧ p4) → False)) ∨ (False ∧ p2))) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217530214208968565650598274301 : ((((p2 → p3) ∧ p5) → p5) → (((p4 ∨ ((p4 ∨ p1) → p4)) → ((p2 → (p3 ∧ True)) ∨ True)) ∨ (p1 ∧ (p2 ∨ (p1 ∨ (p3 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684261178849845828328271360991 : ((((((p5 → False) ∨ ((p1 ∧ p2) ∨ (p2 ∧ ((True ∧ p4) ∨ True)))) ∧ ((p1 → p5) ∨ False)) ∨ (False → (((p1 ∧ p1) → True) → p2))) ∨ p3) ∧ True) := by
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124102951067702615855871813914 : (((((((p3 ∨ False) → p4) → False) → (True → p1)) → False) ∧ ((p3 ∧ ((((p5 → p4) ∨ p5) ∨ p3) ∨ True)) → (p5 ∧ p5))) → (p1 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p3 ∨ False) → p4) → False) → (True → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234716607455423385671000924761 : ((p4 → (p3 ∨ False)) → ((p1 ∧ ((((((p3 ∨ p5) → p5) ∨ (((p4 → p4) → p3) ∧ (True ∨ p5))) ∨ p4) ∨ p3) ∧ p4)) → (p3 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h11 := h1 h10
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h18 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h19 := h1 h18
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- False on the left can always be used.
            apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h23 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h24 := h1 h23
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h26 =>
            -- False on the left can always be used.
            apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h29 := h1 h28
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- False on the left can always be used.
        apply False.elim h31
  case inr h32 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111392449937788725578059674514 : (((p1 ∨ (((p2 ∨ (False → ((p2 ∧ ((False ∧ (((p3 ∧ False) ∧ p2) ∧ False)) ∧ p3)) ∧ (p3 → p5)))) ∨ p2) → p4)) ∧ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170444987789901288913539828024 : ((((p5 ∨ p1) ∨ p3) → (((p4 → (False → (p4 → True))) → False) ∨ (False → p5))) ∧ ((True → ((p5 ∨ (p3 ∨ (p3 ∧ p5))) ∧ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45080100654875445867976410338 : ((((p1 ∧ p5) → (((p2 → (((p5 ∧ (p5 ∧ p2)) ∨ (False → ((False → True) ∧ (p3 → p1)))) → False)) → True) ∨ (p4 ∧ p4))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716381962407402363119563583473 : (((((p4 ∨ p1) ∧ (p2 → p2)) ∧ (((p4 ∨ (p3 ∧ p2)) ∧ ((False ∨ (((p2 ∨ p4) → ((False ∨ False) ∨ p2)) ∧ p4)) ∧ p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41634313548209607854452872016 : ((((p5 ∧ (True ∧ (((True ∨ p2) ∨ p2) → p1))) → (((((False ∧ p4) ∨ (p1 → p2)) → (p4 ∧ True)) → (p4 ∨ p3)) ∨ p4)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265635797134917250551987968429 : (True ∧ (p2 ∨ ((((False ∨ p1) ∧ p5) → (((((((p3 → False) ∧ p2) ∧ (p3 ∨ p2)) ∨ p3) → p4) → ((p4 ∧ p1) ∨ True)) ∨ p1)) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111707260465899385874913932762 : (((((((p5 ∧ p5) → (((p4 ∨ p3) ∨ p1) ∨ (False ∧ ((p2 ∧ False) → True)))) ∧ p3) → (p1 → (p5 ∧ p1))) → p1) ∨ True) ∨ (p2 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41829372178494724465598974255 : (((((p3 → True) → p4) ∧ (p3 ∧ ((p4 ∨ p5) ∧ (((p5 ∧ p4) ∧ (True ∧ ((p1 ∨ p5) → p1))) ∧ ((p4 → p5) ∨ p1))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319049390549315976649969800912 : (p4 ∨ (((p5 ∧ (p3 ∧ (True ∧ p2))) ∨ ((((p3 → (False ∨ p3)) → p1) ∧ False) ∧ ((False ∧ False) ∨ p2))) ∨ (True ∨ ((p3 ∨ False) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315675591905450307126487319561 : (p3 ∨ ((p5 ∧ p5) ∨ ((p1 ∨ ((p4 → (p2 → p2)) ∧ ((p1 ∨ (p2 → p2)) ∨ ((p3 ∧ p2) ∧ p3)))) ∧ ((p5 ∧ (False ∧ p5)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59041025986262270951833443715 : (((p4 ∧ p2) ∨ ((((True ∧ (p5 ∧ True)) → (((p3 → (False ∧ p2)) → p4) ∧ (p4 ∨ ((p3 ∧ (p4 ∨ p2)) ∨ p5)))) ∧ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315108471763153676730790012659 : (p3 ∨ (((p4 ∧ (p1 ∨ (p4 ∨ p4))) ∧ p3) ∨ (False → (False ∧ ((p5 ∧ ((((True ∧ (False → p3)) ∧ True) ∧ False) ∧ (False ∨ p5))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_215819255406469955856000111124 : ((p2 ∨ ((p5 ∨ p5) ∧ p2)) ∨ (((p2 ∧ p1) ∨ ((p5 ∧ p5) ∧ p4)) → ((p2 ∧ (p4 → (p3 ∧ False))) ∨ (p1 ∨ ((p2 → False) → p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



