variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172313044741658422697636792586 : (((p5 ∧ (((p3 ∨ p1) ∨ (p1 → p1)) → p5)) → ((False → (p3 ∧ p5)) → p4)) ∨ (False → ((((p1 → True) → p5) ∨ (p1 ∧ p2)) ∧ p5))) := by
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
theorem thm_5_vars_324560573617700336691123087067 : (p5 ∨ ((True → (False ∧ (p2 ∨ False))) → (p5 ∨ ((p5 ∨ ((p5 ∨ False) ∧ (p2 → (False ∨ ((True ∨ ((p4 ∨ p5) ∧ p1)) ∨ p3))))) ∨ True)))) := by
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
theorem thm_5_vars_221293472983341327041604141073 : (((p3 ∨ p3) ∨ True) ∧ (((((True ∧ False) ∧ (((p2 ∨ p1) ∧ p5) ∧ p2)) ∨ (p2 → p4)) → (p4 ∧ p4)) ∨ (p5 → ((p2 ∨ p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114408019614951929027574978877 : ((((False ∨ ((p1 ∨ p2) ∧ p3)) ∨ ((p1 ∨ (True ∨ ((False ∧ True) → p1))) ∨ (p4 ∨ p1))) ∨ (p3 ∨ ((p4 ∧ p4) → False))) ∨ (p4 ∧ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343608717027512553574303423683 : (p2 → ((p5 → p2) → (p3 → ((((p1 → ((False ∨ ((p5 → p4) ∨ p4)) ∧ True)) ∧ p5) ∨ ((p2 → False) ∧ (p4 ∨ p4))) ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758882823796868368645255649182 : (((p2 ∧ (((((False ∧ True) → (p1 ∧ (p2 ∨ False))) → (p3 → (((p5 → ((p3 → p4) ∨ True)) ∨ p1) → p2))) ∧ (p3 ∧ p4)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135443895724205821388436642044 : ((((((False ∧ (False → ((p3 ∨ False) ∧ p1))) → p2) ∨ (p5 ∨ (p1 ∨ (p3 ∧ p1)))) ∧ p4) → ((True ∧ p1) → p5)) ∨ ((p3 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112445433929011649091451528897 : ((((((p4 ∨ True) ∧ (True ∨ ((((p2 → (True ∨ (False → p4))) ∧ p2) ∨ ((p5 → True) → p1)) ∨ p4))) → p3) ∨ False) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190071193575000354838516889294 : (((((True ∧ p1) → (p4 ∧ (p2 → False))) → p2) ∧ p1) ∨ (((False ∨ (p3 ∧ (True → p1))) ∧ p2) ∨ (False → (p4 ∧ ((p4 ∨ p5) ∨ False))))) := by
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
theorem thm_5_vars_872528634442821144773543326663 : ((((True → ((p4 ∨ ((p2 ∧ True) ∧ (False ∨ False))) ∨ (p5 → (p5 ∧ ((((p4 ∧ True) ∨ (p1 ∨ False)) ∧ (p1 ∧ p3)) → p1))))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((p4 ∨ ((p2 ∧ True) ∧ (False ∨ False))) ∨ (p5 → (p5 ∧ ((((p4 ∧ True) ∨ (p1 ∨ False)) ∧ (p1 ∧ p3)) → p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h7.left
        let h16 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695270784068900431329895776931 : (((((((False ∧ (False ∧ p2)) ∧ (p2 → (True → p1))) ∧ (False → True)) → p1) → ((p1 ∧ ((((False ∧ p4) ∨ p3) ∨ False) → p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191428572597993110118516266322 : (((p2 ∨ p2) → (False ∨ ((p5 ∨ p3) ∨ (True ∨ p2)))) ∨ (p1 ∨ ((((True ∨ (p3 ∨ (p1 → (p4 ∧ p1)))) ∨ p1) → False) ∧ (p1 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789500922410260072111093007118 : (((p5 ∨ (((((p1 ∨ True) ∧ ((p5 → p1) → False)) ∨ p3) → p1) ∧ (((False ∧ True) ∨ p1) → (p2 → (((p3 ∨ p2) ∧ p3) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179059574983037106436804001369 : ((True ∧ (((p1 ∨ (p1 → False)) ∧ (True → (p4 → (p1 ∧ False)))) ∧ p2)) ∨ ((p5 ∨ True) ∨ (((((p4 ∨ True) ∨ p4) ∨ p5) ∨ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168658949927012387809187778186 : ((p4 ∧ (p3 ∨ (p5 ∧ (((p2 ∨ (p1 ∨ False)) → (p1 ∧ (p1 ∧ p3))) ∧ (p2 ∧ p1))))) → (((p5 ∧ p1) → (True → p3)) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : (p2 ∨ (p1 ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340871329150206794232535244877 : (p2 → (((True → (((True ∨ p1) → (p5 ∨ p2)) ∧ (((False ∧ False) → p2) ∧ (p3 → (p4 ∧ p5))))) → (((p3 → p2) → p3) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160827364161418824591480710381 : ((((False ∨ p3) ∨ (True ∨ (p2 ∨ p3))) → (((p3 → ((True ∨ False) ∧ True)) ∨ p5) ∧ (p3 ∧ p2))) → ((((p5 ∨ p4) ∧ p2) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ p3) ∨ (True ∨ (p2 ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308118003845314035586861642666 : (p2 ∨ (((((p4 ∨ ((p3 ∨ p5) ∨ (p3 → p1))) ∧ True) ∨ p5) ∨ (((False → p1) ∧ (False ∨ False)) → ((p1 ∨ (p2 ∧ p1)) ∨ p3))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148102282427818922320506612713 : ((((((False ∧ ((p5 ∧ (p3 ∨ True)) ∧ p2)) ∨ False) ∧ (p5 ∧ (True → p4))) → (p1 → p3)) → (p5 → p4)) ∨ (((p4 ∨ p4) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631761766042842657341989285934 : (((((((((((p1 ∧ True) ∨ p5) → p5) ∨ p5) → p1) ∨ p4) ∨ (False ∨ (((p5 → True) → (p5 ∨ True)) ∨ (p2 ∧ p5)))) → p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185249858337506705197755097734 : ((p1 ∧ ((((p3 ∨ p5) ∨ (True ∧ True)) ∧ (p2 ∧ p5)) ∨ p1)) ∨ (p1 ∨ (((((p4 ∧ p1) ∧ p3) ∧ (p5 ∧ True)) ∧ (p3 ∧ p3)) → p5))) := by
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
  let h12 := h3.left
  let h13 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724339188322958615298872930950 : ((((p5 ∧ (p2 ∧ p1)) ∧ ((((p5 ∨ (((False ∨ (((False → (p4 → False)) ∨ p1) → True)) → False) → p4)) ∧ (True ∧ p5)) ∧ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346300868315390055392095187785 : (p3 → (((p5 ∨ (p1 ∨ (((p2 → (False ∨ ((False ∧ (False → (p2 ∨ (p1 → p5)))) ∧ False))) → (p1 ∧ False)) ∨ True))) ∨ p3) ∨ (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254148960769544556336392265468 : ((p2 ∧ p1) → ((((((p1 → ((p2 ∨ (p4 ∨ ((False ∧ False) ∧ p5))) ∨ (True ∧ p3))) ∧ True) ∨ p5) ∧ True) → (True ∧ (False ∧ p1))) ∨ p1)) := by
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
theorem thm_5_vars_641468876326949353467856104390 : (((((True ∧ p4) → ((p3 ∧ (((False → (True ∧ p2)) ∧ ((p5 ∧ p4) ∨ p2)) ∧ (p2 ∧ (p3 ∧ ((p5 ∨ False) ∧ False))))) → p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55356866661629033577794836923 : (((p3 → (((p5 → p1) → p5) → False)) ∨ (((p5 ∧ p1) → p1) → ((p5 ∧ (((p4 ∨ (True ∧ p4)) ∧ True) ∨ (False ∧ p5))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54429545782424451641461545065 : (((((p3 ∨ True) ∧ (p4 ∨ (False ∨ p2))) ∨ False) ∨ (False → ((True ∧ p4) ∧ ((((p4 ∨ True) ∧ True) ∧ p5) ∧ ((p4 ∨ p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159480268393907096653732395530 : (((((p2 ∧ p3) ∨ (p3 ∨ p1)) ∧ (((True ∨ ((True → (p2 ∨ p5)) → p5)) ∨ p4) ∧ p4)) ∧ True) → (False ∨ (p1 → (True ∨ (False ∧ p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h5.left
      let h21 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h5.left
      let h31 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h34
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h36
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123725105046253689897354136788 : ((((((p2 → (p4 ∧ (True → p3))) → False) → p1) ∨ ((False → p1) ∨ p5)) ∧ ((p2 ∧ ((p3 ∨ False) ∨ True)) ∨ (p5 ∧ False))) → (p3 ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h22 =>
            -- False on the left can always be used.
            apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336202729690349388216677897107 : (p1 → (((False ∧ (((p2 ∧ (p3 ∨ p2)) ∨ (p4 ∨ (True ∨ p1))) → (p3 ∧ (((True ∨ p4) → False) ∨ (False ∧ p4))))) ∨ (p4 ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_733855734770357445899328436691 : ((((p5 ∧ p5) ∧ ((((p3 ∨ (p3 → p2)) ∧ (False → (((p3 ∧ (p5 → p3)) ∨ p2) ∧ p2))) ∧ ((p1 ∧ p5) ∧ (p2 ∨ True))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164607780226590162291153646370 : (((p1 ∧ ((((p3 → (True ∨ p5)) → p3) ∧ ((p5 ∧ (p2 → p4)) ∧ p4)) ∨ p1)) ∧ p1) ∨ ((True ∨ p2) ∧ (p5 → (p5 ∧ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46876381291073610765653786313 : ((((p5 → (((((p1 ∨ True) ∧ False) → p3) ∧ ((False → p5) ∧ False)) ∨ (p4 ∧ (((p4 ∨ p5) ∧ True) ∧ p2)))) ∧ False) ∨ (False ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695650752223522023571638425542 : ((((((p2 ∧ (p4 → p5)) ∨ (False ∨ p2)) → ((False → p1) ∨ (p1 → p1))) → (((p2 ∨ p4) ∨ ((p2 ∧ False) ∨ False)) ∧ (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740837932474218217360495471320 : ((((p3 ∨ False) ∨ ((p4 ∧ (p5 ∨ ((p3 → ((p1 ∨ (p5 → p4)) ∧ (p4 → (p4 ∨ True)))) → True))) ∨ (p4 ∨ ((p2 ∨ False) ∨ True)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_214518989895573155913140700449 : (((p4 ∧ p3) ∧ (p1 → p4)) ∨ (p1 ∨ (((False → (p1 → (((p5 ∨ (((p3 ∨ True) ∧ True) ∨ (True ∧ p2))) ∧ p3) ∨ p3))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55514710788882372769929532275 : ((((p3 ∧ p2) ∨ (True → (True ∨ True))) → (p2 → (((p1 ∨ p2) ∧ ((p2 ∨ False) → (((p4 → p5) ∨ p2) → (p1 ∧ p3)))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338413982526687023342291663775 : (p1 → (((p1 ∧ True) → (p5 → p2)) → ((p5 → (p3 ∨ ((((p5 ∨ (p2 ∨ p4)) ∧ (p1 → p5)) → p4) ∨ (p3 ∨ p2)))) ∨ (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352230005918507195453083710872 : (p4 → (((False ∧ True) ∧ (True ∧ p5)) ∨ (((p3 ∧ (((p5 ∨ ((p2 ∧ p1) ∨ (p1 → p2))) → ((True ∧ True) → p3)) ∨ p5)) ∨ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142531110023605623121299528000 : ((True ∨ ((p1 ∨ ((p1 → p4) ∧ ((((False → p1) ∧ p2) → p4) → (p2 ∧ p2)))) ∧ (True ∧ ((True ∧ p3) → p1)))) → ((True → False) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h8.left
      let h18 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356520022390276620549800231685 : (p5 → ((((True ∨ p3) → ((p2 → (p1 → p3)) ∨ p2)) ∧ p2) ∨ ((((False ∧ ((p5 ∧ (p1 ∧ False)) → (True → p5))) ∧ p4) ∧ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77878881243477771726673602832 : (((p1 ∨ ((p1 ∨ (p5 ∧ ((p5 ∨ p3) → (p3 ∨ ((((p4 ∨ p5) ∨ True) ∧ p4) ∧ False))))) ∨ ((p2 → (p4 → p2)) ∧ True))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p1 ∨ (p5 ∧ ((p5 ∨ p3) → (p3 ∨ ((((p4 ∨ p5) ∨ True) ∧ p4) ∧ False))))) ∨ ((p2 → (p4 → p2)) ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165827365389754173098173442457 : (((False → (p1 ∧ p1)) ∧ ((False ∧ False) ∨ (((False ∧ p4) ∨ p4) ∨ (True ∨ (p5 ∨ p5))))) ∨ (p5 ∨ ((False → (p3 → False)) ∨ (p4 ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165520939526347839009374890803 : (((((True → p5) ∧ p1) ∨ ((p4 → (False ∨ True)) → True)) → (((p5 ∧ p5) → p5) → p2)) ∨ (False ∨ (p3 → (p1 → (p3 ∨ (True ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593981785706850193995938947225 : (((((True ∧ ((p4 → (p2 ∧ p4)) → (False ∧ ((((p5 ∨ p5) ∧ p3) ∨ (False ∧ p3)) ∨ False)))) ∨ ((p4 ∧ (True → p1)) → p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689966355500903385306949994118 : ((((False ∧ ((p4 ∨ (p3 → True)) → ((p2 ∧ ((p4 ∧ p3) ∨ (p2 → p3))) ∨ p5))) ∨ (p2 ∧ (p1 ∨ ((p5 → p1) ∧ (False ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175208971731706381423369414230 : ((False ∨ (p1 ∧ (p4 ∧ ((False ∨ p1) ∨ (p2 ∨ ((True → p4) ∧ (p2 ∨ p4))))))) → ((p5 ∧ (p5 ∨ (p2 → (False → (p3 ∨ True))))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672171020850510072382459178000 : (((((True ∨ (True → (p3 ∧ ((p3 ∧ (p1 ∨ (p3 → p3))) ∨ (((p1 ∧ True) ∧ (p5 ∨ False)) → True))))) ∨ p4) → (p4 ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232319398362948788062423174238 : (((p3 → p3) → p5) → ((True ∧ ((((p1 → p2) ∨ (False ∧ (p1 ∧ (p2 ∧ False)))) ∧ (p4 ∧ p1)) ∨ ((p4 ∨ (p5 ∨ p1)) ∨ p5))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149450574561828398553938078846 : ((False ∧ ((p4 ∧ (p5 ∧ ((p1 ∧ ((p3 ∧ p1) → (p4 ∨ True))) ∧ ((p3 ∨ (p4 → p4)) ∨ p1)))) → p3)) ∨ (False → ((p1 ∨ False) ∧ p2))) := by
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
theorem thm_5_vars_53957990578052201817913038391 : (((((p1 ∧ (p5 ∨ (p4 ∧ (p2 ∨ p1)))) ∨ p1) ∧ p4) → ((((p2 ∧ (((p5 → p3) ∨ True) → False)) ∨ p1) ∧ (True ∨ True)) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732894822763908333112934990409 : ((((p2 ∧ p1) ∧ (((p5 ∧ p4) ∧ True) → ((((p5 → (p2 ∨ ((p1 ∨ p2) ∨ p4))) ∧ p1) ∨ p2) → ((False ∧ (p4 ∧ p1)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314222625003108966832107632003 : (p3 ∨ ((((p4 → ((p4 ∨ p2) ∨ (False → ((p4 ∧ (p3 ∨ ((False → False) ∨ False))) ∧ (p3 ∧ True))))) → p2) ∧ p5) ∨ ((True ∨ p4) ∨ False))) := by
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
theorem thm_5_vars_330251144433088624400787004779 : (True → (False ∨ ((True → (((False ∧ (p3 ∨ ((False → (True ∨ p4)) → p1))) ∨ p5) ∧ ((p4 ∧ p5) → (False ∧ False)))) ∨ ((True ∨ p5) ∨ p3)))) := by
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
theorem thm_5_vars_171424716400765331882789077070 : ((((False → p3) ∧ (((((p5 ∨ (True → p3)) ∧ p3) ∨ False) → False) ∨ p4)) ∧ p4) ∨ (((((p3 ∧ p5) ∧ p2) → p3) ∧ (p4 ∧ p2)) → p4)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247564744064441829701657301052 : ((False ∨ p4) ∨ ((p3 ∨ False) → (p4 → (p3 → (((p2 ∧ ((False ∨ (p4 ∧ p1)) → ((False → (p1 → False)) ∧ False))) ∨ (False ∨ p4)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233686527163141559300544947756 : ((p2 ∨ (p2 → True)) → (((p3 → ((p4 ∧ (((p4 ∨ True) ∨ p3) → p4)) ∨ True)) ∨ (p4 ∧ ((p2 ∨ (False ∧ (p1 → p2))) ∧ True))) ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65557838603788633115533294425 : ((p3 ∨ (p1 → (False ∨ ((((p3 ∧ ((p3 ∧ True) ∧ (p1 ∨ (True → (p1 ∨ (True ∧ p4)))))) ∨ (p2 ∧ p1)) ∨ p2) ∨ (True → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191990339762951433306300784430 : ((p1 → ((((p2 ∨ p2) → (p2 ∨ p4)) → False) ∨ True)) ∨ (False ∨ ((p3 ∧ ((p3 → ((p5 → p1) ∧ p1)) ∧ ((p3 → False) ∧ p4))) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56501911365420034722542376154 : (((p2 ∧ ((p1 ∨ False) → p3)) → (False ∨ (((p3 → ((((p1 → p2) → (p3 ∧ (p2 ∨ True))) → p5) ∨ p4)) → p5) ∨ (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207114778534095432328715926350 : (((p3 ∨ ((p3 ∧ p5) ∨ p5)) ∧ p5) → (((p2 ∨ p2) → (((p4 ∧ (p2 ∧ ((((p2 ∧ False) ∧ True) ∨ False) ∧ False))) ∨ False) ∧ False)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256837408298783367306237884431 : ((p1 ∨ p3) → ((p4 ∨ (((True → False) ∨ ((p2 ∨ ((False ∨ p4) ∨ True)) ∨ (((p3 ∧ p5) → True) ∧ True))) ∧ p5)) → ((p4 ∨ p3) ∨ p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- Disjunctions on the left can always be decomposed.
              cases h1
              case inl h21 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h21
              case inr h22 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h20
          case inr h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h24
            case inr h25 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62610715269128789912099956873 : ((p4 ∧ (((((True ∧ (((((False ∧ p5) → True) ∧ True) ∧ (True ∨ False)) → p3)) ∨ p3) ∧ (True → (True → (p4 → p5)))) ∨ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40832470204055315877670125247 : ((((p1 → ((p4 ∧ p5) → ((False ∨ ((True ∨ (((False ∧ p5) ∧ (p1 ∨ (p2 → p1))) ∧ (True → p5))) ∨ p4)) ∧ True))) → False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599502943372365076122177399783 : (((((p1 ∨ p5) ∨ ((((((True → p4) ∧ True) ∧ (p5 → p3)) ∧ True) ∧ ((((True → False) → True) → (True ∧ p2)) ∨ p2)) ∨ p1)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217868090619852548397613713436 : (((False → (p3 ∨ p4)) → p2) → (((((p3 ∧ (p5 → p1)) → (p3 ∧ False)) ∨ p3) ∧ (True ∨ ((p4 → (p2 → False)) → (p4 ∧ p3)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p3 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355411553990961326848250330580 : (p5 → ((((False ∨ ((True → ((True ∧ p1) → p2)) → (p2 ∧ ((p2 → p1) ∧ (p1 ∨ (p5 → p5)))))) ∨ (p5 ∨ p2)) ∧ True) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197792490026733052414060213868 : ((((p4 ∨ p4) ∧ p2) ∨ ((p4 ∧ p3) ∧ p3)) ∨ (p4 → (((((((p5 → p4) → p4) → p4) ∨ p2) ∨ (False ∧ (p3 → False))) ∧ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177963549069620838437444002567 : ((((p3 → False) ∨ ((p1 ∨ (((p3 → p5) → p3) → False)) ∨ p2)) ∨ True) ∨ (((False ∨ p2) ∧ p2) → (p2 ∧ ((p1 ∨ (True → p5)) ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53899246322783023599713440521 : (((p2 ∧ (p3 ∨ (True → (False ∨ ((p4 → p5) ∨ True))))) ∨ (((p3 ∨ p2) ∧ (p1 ∨ (p5 ∨ (p4 ∧ True)))) ∧ ((p2 ∧ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308640132190625925245337144412 : (p2 ∨ ((False ∧ (((((p1 ∧ True) ∨ (p5 ∧ p1)) → p2) ∧ (p1 ∨ (p5 ∨ (p5 → (p1 ∧ ((p4 ∧ (True → p5)) ∨ p3)))))) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160985431436400083940464256274 : ((((p1 ∧ p1) ∧ False) ∨ ((p5 ∧ (False → p2)) ∧ ((p5 ∧ p1) → (p2 ∨ (p4 → (p5 ∨ p2)))))) → ((((p4 ∧ False) → p1) → False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156885709102011199048285918425 : (((((p4 → ((False ∨ (((p1 ∨ False) → True) ∨ ((True ∧ p2) → p1))) ∧ p1)) → p2) ∨ p4) ∨ p2) ∨ (p3 → ((p1 ∧ p5) → (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158103511541117505560887220047 : (((((p5 ∨ p2) → p2) → p3) ∧ (((p4 ∨ (True ∨ p5)) → False) ∧ (((p4 → p5) ∨ p3) ∨ True))) ∨ ((p3 → True) ∨ (p2 ∨ (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149409469869401960814390357709 : ((True ∧ (((False ∨ (((((p3 → p3) → p2) ∧ p3) → p4) → (p1 ∨ p1))) ∧ p4) ∨ ((False → p1) ∨ p5))) ∨ (((p1 ∨ p2) ∨ p5) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208468247873454594486704208185 : (((p3 → p2) ∨ ((True ∧ True) → False)) → ((p1 ∨ True) → (((False ∧ (p1 ∨ (p1 → ((p1 → p1) → p5)))) ∧ p3) ∨ (p2 → (p4 → p2))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (True ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (True ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264039409488659805575325147040 : (True ∧ (((False ∧ ((False ∧ p3) ∨ (p2 → p5))) → (True ∧ False)) ∧ (((p4 ∧ p3) → (((p4 → p1) → ((p5 ∨ True) ∧ p3)) → False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161517277816527523517033770580 : ((p4 ∧ (p4 ∧ ((p3 ∧ p4) ∨ ((p4 → ((True ∧ ((True ∧ p4) → p2)) ∧ False)) ∧ (p1 ∨ False))))) → (p2 → (p2 → (p3 ∧ (p3 ∧ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h30 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h31 := h27 h30
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803861401633820560954982765987 : (((p3 → ((True → (p2 ∧ (((p3 ∧ (p4 ∧ ((p1 → p4) → True))) → ((p1 → p3) ∨ (p5 ∧ (p4 → p5)))) ∨ False))) ∨ (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603646821696276240499093702939 : ((((p4 ∨ (((p5 ∨ (True ∨ ((p3 ∧ (p5 ∨ ((p2 → p4) ∧ (p1 ∧ p5)))) → p4))) → (((False ∧ p2) → p4) ∧ p2)) ∧ p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746604878011506414970239547797 : ((((p3 ∨ True) → (p1 → (((((p3 ∨ ((((p3 ∨ p3) ∧ p1) → p5) → (p1 → p5))) ∨ p4) ∧ (False ∧ False)) ∧ (p2 → True)) ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16020706714614310706736396609 : (((True → ((p2 ∧ ((True ∨ True) ∧ False)) ∧ (((p1 → (p2 ∨ p2)) → (p3 → p1)) → (((True ∧ True) → p2) ∧ p2)))) → (False ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227474834080367675672260243413 : ((True ∧ (p3 ∧ p1)) ∨ ((p2 ∧ (True ∨ ((p1 ∧ ((p4 ∧ ((p1 ∧ (p3 → (p5 ∧ False))) → p1)) ∨ p4)) ∨ (p4 → True)))) → (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625997834454952806658374103226 : ((((p2 → ((p4 ∧ (p3 ∨ (p3 → (p1 ∨ p3)))) → (((((p4 → p5) → p1) → ((True ∧ p1) ∨ False)) ∨ (True ∨ True)) ∨ p5))) ∨ False) ∨ p1) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
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
theorem thm_5_vars_444457404815986357059197188878 : ((((p5 ∧ ((p1 ∨ (p5 ∧ p1)) ∧ (((((p3 → p3) ∧ (p3 ∨ p5)) ∨ (p3 ∨ p2)) ∧ (p4 ∨ p2)) ∨ True))) ∨ (True → (False ∨ True))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_612006280610763761177572427499 : ((((((((True → p4) ∧ ((((((p5 → p5) → p1) ∧ p2) → p1) ∨ (p4 ∧ (p3 ∨ p2))) ∨ p5)) ∧ True) → False) ∧ (p5 ∧ p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_41539138172500165396049111262 : ((((((p3 ∧ p2) ∨ (p2 ∨ (p2 ∨ p1))) → (p1 ∧ p2)) ∨ (False ∨ (((p4 → p3) ∧ ((True ∨ (p4 ∧ p4)) → p2)) → p5))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215561255966330944736340566588 : ((p5 ∧ ((p4 ∧ p1) ∨ p1)) ∨ (((((False ∧ True) ∨ True) ∧ p2) → False) → ((True → p1) ∨ ((p5 ∨ (False → p2)) ∨ ((True → p2) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621933984183495789154212003560 : ((((p1 ∧ (p5 ∧ (p3 ∨ (((p5 ∨ False) → (((p1 ∧ (p4 ∨ (p4 ∨ (p4 ∨ True)))) ∧ p5) → ((p5 ∧ p1) → True))) ∧ p3)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255504148294083051007893667492 : ((p5 ∧ p2) → ((((p3 → ((p3 ∨ True) → p3)) ∨ p3) → ((p5 → (p4 ∨ (p5 → p3))) → False)) ∨ (True ∧ (p2 ∨ ((p5 → False) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351625514590728016695031998022 : (p4 → (((((False ∨ (((p1 ∨ p5) ∧ p1) → ((p4 ∨ p5) → True))) → p1) ∧ p3) ∨ p3) ∨ (True ∧ (((True ∨ (True ∨ p3)) ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_784987125942865482319671922815 : (((p3 ∨ (p4 → (p1 ∨ (((False ∨ p5) ∧ p5) → ((p3 ∧ p5) ∨ (False ∨ (((p4 → p2) → False) ∨ (((True ∧ p1) ∨ p5) ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305186654079126388451440738318 : (p1 ∨ (((p5 ∨ p2) → (p2 → ((((p3 ∨ False) ∨ p5) ∧ p5) → (p3 → (((False → False) ∧ False) ∨ True))))) ∨ (((p4 ∨ p2) ∧ p3) ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
theorem thm_5_vars_257001765987379538837844727704 : ((p2 ∨ True) → ((((p5 ∨ (((((((p1 ∨ False) → p5) ∨ (True → (p1 ∧ p5))) ∨ False) ∨ p1) → False) ∨ True)) ∨ (p1 ∨ False)) ∨ True) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165639668706589591303078984870 : (((False ∨ (p5 ∧ (p1 ∨ (p4 → False)))) ∧ ((p4 → (p2 ∨ (p2 → (p4 → p3)))) ∧ p1)) ∨ ((p5 ∨ (True ∨ ((p3 → p2) ∧ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_320452082386001100910285561499 : (p4 ∨ ((p5 ∨ False) → ((((p1 → p1) ∧ (((((p5 ∨ p4) → True) ∧ p5) ∧ p3) → (p2 → p5))) → False) → (p2 ∨ ((p1 → p3) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 → p1) ∧ (((((p5 ∨ p4) → True) ∧ p5) ∧ p3) → (p2 → p5))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h4
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197821064004859751300089782390 : ((((p3 → p5) → p3) ∨ ((p1 ∧ p1) ∧ p4)) ∨ (False ∨ ((False → ((p5 ∧ ((True ∧ (((True ∧ True) ∨ p5) ∨ p4)) ∧ True)) ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300671296809803886038651396307 : (False ∨ (((True ∧ (((False ∧ p1) ∨ p4) ∨ ((p1 → False) ∨ ((p2 → p1) ∧ (True ∨ p1))))) → p5) ∨ (p4 ∨ (p3 ∨ (p4 ∨ (True → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345688216318390290174992016596 : (p3 → ((p4 ∨ ((((p1 → (p3 ∧ (True ∨ (p4 ∨ (False ∨ p2))))) → (p2 ∧ (p5 ∧ p1))) ∧ (p5 ∧ False)) ∨ (p5 ∨ (p4 → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178759206779992217683187002035 : ((((p3 ∨ p5) ∨ p5) ∧ (False ∧ (p5 ∧ (((p2 → p5) → p1) → p2)))) ∨ ((p2 ∨ (((p3 ∨ p4) ∧ ((False ∧ p1) ∨ p2)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



