variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160145620954422831969613838267 : ((((p3 → (p3 → (False ∨ (p1 ∨ (((p1 → p2) → (p4 ∧ p5)) ∨ True))))) → False) ∧ (False → p4)) → ((((False ∧ p2) ∧ p4) → p5) ∧ p3)) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p3 → (p3 → (False ∨ (p1 ∨ (((p1 → p2) → (p4 ∧ p5)) ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h9
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57287879134339591510893946920 : ((((p1 → True) → p4) ∨ (((p1 ∧ p1) ∨ ((p3 → ((((p4 ∧ (p2 → False)) ∨ False) → (p5 ∨ p4)) ∨ p3)) ∨ p1)) ∧ (p3 ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308534905395166256790694596064 : (p2 ∨ ((((((p5 → (True → (p1 ∧ False))) ∨ p4) → p5) → (True ∧ p3)) ∨ ((True → (p4 ∧ ((False → True) → p2))) → (p2 ∨ p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190577600192891485681405461919 : (((((p4 ∧ p2) ∧ p1) → (True ∧ (p3 ∧ p4))) → p1) ∨ ((((p1 ∧ ((p4 ∨ p3) ∨ ((p1 → p2) ∨ False))) → False) ∧ p5) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652104466759208440073128536469 : ((((p1 ∧ (((((p1 → (p2 ∧ False)) ∧ False) ∧ (False ∨ ((True → p2) ∧ ((p3 ∨ p2) ∨ (p5 ∧ True))))) ∨ p4) ∨ p2)) ∧ (p1 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53266753720748664049494653847 : (((True ∧ (((p4 ∧ (True ∧ p2)) ∧ ((False ∧ p2) → True)) → p3)) ∨ (p4 ∨ (p2 ∧ (((True ∧ True) ∧ p5) ∨ (p1 ∧ (p2 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119033548180684875708048332825 : ((p1 → (((False ∨ (p2 ∧ ((((p5 ∧ p4) ∨ p4) ∧ p3) ∧ (((((p2 ∨ p4) → p3) → p2) ∧ p3) ∨ p2)))) ∧ p1) ∧ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351415005581848063506472524444 : (p4 → (((p5 → p5) ∧ (True → (((p1 ∨ (p5 ∨ p2)) ∧ ((p4 → p2) ∧ (p2 ∨ (p3 ∨ False)))) ∧ p2))) ∨ (((p3 → p2) → p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932331901387494683741213609446 : ((((((p3 ∨ False) → (True ∨ p1)) → (p2 ∧ p3)) ∧ (((False ∨ p5) → ((p2 ∧ p5) ∨ p5)) ∧ (((False → p2) → p1) ∨ (p5 ∧ p1)))) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ False) → (True ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h7
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : ((p3 ∨ False) → (True ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h16
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901955037018103936220652898263 : ((((((True ∧ (p3 ∧ False)) → ((((False → (p1 → True)) ∧ True) → (p1 → (p1 ∧ True))) ∨ p3)) → False) ∧ ((p3 ∨ (p3 ∧ p5)) → p2)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ (p3 ∧ False)) → ((((False → (p1 → True)) ∧ True) → (p1 → (p1 ∧ True))) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299061198283816996593914661390 : (False ∨ ((p2 → ((((p5 ∧ p4) ∧ (False → ((True → (False → p1)) ∧ p5))) ∨ (p4 ∧ False)) → ((p1 ∨ False) → (p1 ∧ (p5 ∧ p1))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- False on the left can always be used.
      apply False.elim h32
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302560824404570618952050422990 : (False ∨ (p1 ∨ ((p3 ∨ (((p1 ∧ (p3 → True)) ∨ ((p4 ∨ p4) → ((((p2 ∧ p1) ∧ p3) ∧ False) → p5))) → ((False ∧ True) ∨ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793628252971128457282788429356 : (((True → (p4 ∨ (((p5 → p1) ∧ (p3 ∧ p2)) ∨ ((((p3 ∨ p2) ∨ False) → p3) ∨ (p4 ∨ (p2 → ((False ∧ True) ∨ (False ∨ True)))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171624907195059516661687086214 : ((((p3 ∨ (p3 ∨ p2)) ∨ (((((p3 → False) ∨ False) ∨ True) ∨ p2) ∨ False)) ∨ True) ∨ ((p4 ∧ (p4 ∨ (((False ∨ p1) ∧ p5) ∨ p2))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317509611861575622880805744085 : (p4 ∨ ((p1 ∨ ((p3 ∧ p4) ∨ ((p5 → (p2 ∨ p2)) ∨ (True ∨ ((p1 ∧ (True ∧ ((p2 → ((p5 ∨ False) → p1)) → True))) → p3))))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257321639930291661609780249691 : ((p2 ∨ p4) → (((p3 ∧ (p4 ∧ (((p2 ∨ ((p1 ∧ (p1 → p3)) ∨ p3)) ∨ ((p3 → p5) ∨ p5)) → p3))) ∧ True) ∨ ((p2 → True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781111309897436202320462658706 : (((p2 ∨ ((p1 ∨ p3) ∨ ((True ∨ False) ∧ ((((True ∧ p3) ∨ ((p4 ∧ False) → p2)) → (False ∨ ((p5 ∨ p5) → (p3 ∧ p4)))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65343055469549526230184868040 : ((p3 ∨ (((((p2 ∨ ((p2 → p1) → False)) ∧ (p3 ∨ ((p1 ∧ p5) ∧ p5))) → p2) ∧ p4) ∨ (((p5 ∨ (p2 → p5)) ∨ True) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_227456443361251595713533005649 : ((True ∧ (False ∧ True)) ∨ (((p2 → (((True ∨ p5) → (p2 → p3)) → True)) → ((False ∨ True) ∧ p2)) → (p1 ∨ ((p5 ∨ (False ∨ True)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((True ∨ p5) → (p2 → p3)) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678384761390707257017225970400 : ((((((p2 ∧ False) ∨ ((p1 ∧ p3) → p5)) → (p1 → ((False ∧ ((False → p5) → (p3 ∨ p3))) ∧ p2))) ∨ (True ∨ (True ∨ (p4 ∨ p4)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_259324170158891802393493004857 : ((False → p2) → ((((False → p1) ∧ p1) → ((p4 → (True → True)) ∧ (True → (p4 ∨ (p3 ∨ ((True → p1) ∨ (p2 ∨ True))))))) → (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192365674336635987874995276377 : (((p3 → (((p1 ∨ p5) → p3) ∧ (True ∧ p2))) ∧ p3) → (((p5 ∨ ((p2 → False) ∧ (p1 ∧ p4))) ∨ (p3 ∧ ((p2 ∧ p2) → False))) → p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h18 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h19 := h16 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h28 := h25 h27
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606868361410605771456804018439 : (((((((p1 ∨ ((False → (((p3 ∧ (p2 ∧ p5)) ∧ p1) → ((True → p2) ∧ p3))) ∧ p2)) ∧ p2) → (p4 ∨ (p4 ∧ p4))) ∧ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154224475668782754821819716154 : (((((p5 ∨ (((p2 ∨ p1) ∧ p1) → (p1 ∧ p2))) ∧ p5) → (p1 ∧ (False ∨ (p4 → p4)))) ∨ True) ∧ (True ∧ ((p3 → True) ∧ (True ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207701325583613802832656971429 : (((True ∧ ((p2 ∧ p4) → p4)) → True) → (((p5 ∨ (p3 → p3)) → (p5 ∧ (((((p5 ∨ p2) → True) → p4) ∧ True) ∧ False))) → (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165237139434782114584707604515 : (((False ∧ ((p4 → ((p3 ∨ (p4 → p2)) → (p5 ∧ p2))) → (p1 ∧ True))) ∨ (False → p3)) ∨ ((False ∨ (p2 ∧ (p5 ∧ (True ∨ False)))) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246678777269177718827699835673 : ((p5 ∧ p4) ∨ ((((((False → ((False ∨ p2) ∧ False)) → ((p1 → False) → True)) → (p1 → ((p1 ∨ p4) → p2))) → False) ∨ (True ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785630906646648324820334317044 : (((p4 ∨ (((p1 ∨ ((((False ∨ (((False → (False → (p5 → p1))) ∧ p5) ∧ True)) ∨ p3) ∨ (p4 ∧ True)) ∧ (p5 ∨ p1))) ∨ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115314803353481086891553222425 : ((((False ∧ ((False ∨ p5) ∧ p4)) ∨ ((p3 → p5) ∨ p2)) → ((p5 → (True → (((p5 → False) ∧ p2) ∨ p1))) ∨ (p4 ∨ p3))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338678131736721529783144802926 : (p1 → ((True ∨ p5) ∧ ((((((False → p3) ∧ (p2 ∧ (p5 → (True ∨ ((p4 ∧ p2) ∨ (p3 → p3)))))) ∧ False) ∧ p2) ∨ (p3 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50717438103424029469177933945 : ((((True → False) ∨ (((p3 → p5) → True) → ((p4 ∨ (p1 ∨ p5)) ∨ (False ∨ (p5 → (p1 ∨ True)))))) → (p3 ∧ (p3 ∧ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207264635592650708822049651799 : (((((p3 ∧ p4) ∧ True) → p3) ∨ p1) → ((False ∨ (p1 ∧ (((p5 ∨ (p5 → ((p2 ∧ p5) → (p2 ∧ p5)))) → p5) → (p4 ∧ p3)))) ∨ True)) := by
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
theorem thm_5_vars_174667135583756004429643097438 : (((p5 ∧ (p3 → p1)) ∧ ((p4 ∧ (p5 ∨ (p4 ∨ (p5 ∧ p4)))) ∨ (p1 ∧ False))) → (((True ∨ p2) ∧ p2) → (((True ∨ p1) → p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h15 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h19 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h19
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h25 := h3 h24
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h38 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h39 := h3 h38
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h42 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h43 := h3 h42
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h44 =>
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h47 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h48 := h3 h47
          -- One of the premise coincides with the conclusion.
          exact h48
    case inr h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h49.left
      let h51 := h49.right
      -- False on the left can always be used.
      apply False.elim h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344677738553849431028328814892 : (p2 → (p2 → (((((p2 → False) ∨ p2) ∨ p3) → p2) → (p1 → ((p1 ∧ ((p3 ∧ False) → p5)) → (p5 ∨ (p1 ∨ (p4 ∧ (p5 ∨ p2))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9834562036571740321370480264 : (((True ∧ ((p1 ∨ (p5 ∧ True)) → ((((True ∧ ((True → p5) ∧ False)) ∨ p5) ∨ ((p4 ∧ p1) ∧ (p3 → (False ∧ p4)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605120866311315029803773709581 : ((((p2 → ((((((((False ∧ (p4 ∧ True)) ∧ True) ∨ p2) → p2) ∧ (p5 → p2)) ∧ (p5 ∧ True)) ∨ False) → ((p2 ∧ p2) → p1))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311075181920312347028774120040 : (p2 ∨ ((p2 ∨ p5) ∨ ((p3 ∨ (p3 ∨ (True → p4))) → (((p1 → (True ∨ ((((p5 ∨ False) → p4) → p1) ∨ p1))) → p5) ∨ (p5 → True))))) := by
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
theorem thm_5_vars_327011736105120172380302845310 : (True → (((((p1 ∧ (p3 ∨ p4)) ∨ p2) ∨ ((((False ∨ False) ∧ False) → (p5 → True)) ∧ p3)) → ((p3 ∧ (True → p2)) → (p2 ∨ p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h12 := h5 h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66591566657743278692941677779 : ((True → ((((((p3 → p1) ∧ (p5 ∨ (p1 ∧ (False → p2)))) ∧ p5) → False) ∨ (True ∨ ((True → p5) ∨ p2))) ∨ ((p4 ∨ p2) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49128441545619592196577888644 : ((((((p2 ∨ p2) ∧ p1) ∧ ((p4 → p2) ∨ (True ∨ (p3 ∧ p5)))) ∨ (p2 ∨ ((p4 ∨ (p3 → p2)) → p2))) ∨ ((p1 ∨ False) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146923215989866239650295021945 : ((((True ∧ (((p2 ∨ (p3 ∧ False)) ∨ p1) ∧ (((p5 → ((True ∨ True) ∨ p1)) ∨ False) ∨ p1))) ∧ False) ∧ p5) ∨ (p2 → (p1 → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193489581095074891633239467654 : (((p1 ∨ True) ∨ (((p4 → p1) ∨ (True → p5)) ∧ p5)) → (p3 ∨ ((p2 ∧ (True ∨ (p1 ∧ ((False → p1) ∧ (p1 → (False ∨ p1)))))) ∨ True))) := by
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254389765743440620901601872067 : ((p2 ∧ p5) → ((((((True → (True ∨ (p4 ∧ p5))) ∨ p4) → (p1 ∨ ((p1 ∨ p5) ∧ (False → (p2 ∨ (p5 ∨ p5)))))) ∨ p1) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_519108314176898580054497501239 : ((((True ∨ p3) → (((p2 ∧ ((p3 ∧ (p3 → (p3 → (p5 ∨ p5)))) → (((p4 ∨ p1) → p1) → False))) ∨ True) ∧ ((False → p3) ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666380683156852428250179983037 : (((((((p5 ∧ ((p2 → (False → p3)) ∧ True)) ∨ ((True ∨ p1) → p3)) → (p2 ∧ False)) ∨ (p4 ∨ (p1 ∧ p4))) ∧ ((p1 ∨ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737821030690169945900778768007 : ((((True ∧ False) ∨ (p3 ∧ (((p5 ∧ ((p5 ∨ p3) → False)) ∧ (((p2 ∨ p5) → (p3 ∨ p1)) → (p1 → p4))) ∨ ((True ∧ p5) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689880267908137934247371022775 : (((((p4 → p1) ∨ (p2 ∧ ((p1 ∨ p4) → (((p4 ∧ p4) → (p1 ∨ p5)) ∨ p4)))) ∨ ((p2 ∨ ((True ∨ (p5 → False)) ∧ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173477867692853475553463340997 : ((((((p2 → p3) ∧ ((True ∧ (p3 → p2)) ∨ (True ∨ p3))) ∧ p3) → p2) ∧ p1) → (p2 → ((True → ((p5 ∨ (p4 ∧ p2)) ∧ False)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258753937950463014075503992201 : ((True → True) → (p2 → ((p3 ∨ False) ∨ (((((p1 → (p4 ∧ p1)) ∨ (((p5 → True) ∨ p2) ∧ p3)) ∧ p3) ∧ p3) → ((p1 ∨ p4) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75766453190652785884764665496 : (((((p1 → ((False ∧ (p1 → (p1 ∨ p3))) ∧ ((True ∨ p3) ∨ False))) ∨ (((p1 ∨ (p3 ∧ True)) ∨ p3) ∧ (p3 ∨ True))) ∨ True) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → ((False ∧ (p1 → (p1 ∨ p3))) ∧ ((True ∨ p3) ∨ False))) ∨ (((p1 ∨ (p3 ∧ True)) ∨ p3) ∧ (p3 ∨ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135566726041853900335094199266 : (((p2 → ((p4 ∨ ((p5 → p3) → (p4 ∨ ((p1 ∧ p1) ∨ p5)))) → (p3 ∨ p4))) ∧ (((p2 → False) ∨ p5) ∨ p4)) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337461195476558969484419460334 : (p1 → ((p4 ∨ (p3 → (((p5 → p2) ∨ ((((p2 → p3) ∧ ((True → (False ∨ True)) ∨ True)) ∨ p1) ∨ p4)) → p3))) → ((p5 → p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214668718529751347899505532987 : (((p4 → False) ∧ (p3 → p5)) ∨ ((p5 → ((((p1 ∨ p2) ∨ (((False ∨ (p2 → ((p4 ∨ True) ∨ False))) → p2) ∨ True)) ∨ p3) ∨ p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115339202560179366400357497231 : (((p3 ∨ (((True ∨ (False ∧ (p4 ∨ p5))) → p1) → p4)) → ((p1 → p5) ∨ (((p1 ∧ True) ∧ (p2 ∨ False)) ∨ (p5 ∨ True)))) ∨ (p5 ∧ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228986375208195087137132843617 : ((p5 ∨ (True ∧ False)) ∨ ((((p1 ∨ ((((((((p5 ∧ False) ∨ p2) ∨ p1) → (True ∨ True)) ∧ True) ∨ p1) → p2) ∨ True)) → p5) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_301290333859892388027846728703 : (False ∨ (((p3 → (True ∧ p2)) ∨ (p5 → True)) → (p4 ∨ (((False ∨ (p5 ∨ p1)) → (p5 ∧ ((p5 → ((p2 ∧ p1) ∧ p5)) ∨ True))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124736942049354525954199122853 : ((((True ∨ (p3 → p2)) → p4) ∧ ((False → (((p1 ∧ ((p5 → (False ∨ p4)) ∨ True)) ∨ p4) ∧ False)) ∨ ((p3 → p1) → p2))) → (p4 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p3 → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (p3 → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300068372317899512886198263655 : (False ∨ (((True ∧ (((((False ∨ (p1 → True)) → (p1 ∧ p3)) ∧ (p2 → ((p1 ∨ True) → (p2 ∧ p5)))) ∧ p5) → p3)) ∨ p5) ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47419425885649405391480707799 : (((p1 ∧ ((((p3 ∨ True) ∧ (((False ∧ ((p5 ∧ False) ∨ p5)) ∨ (p2 ∨ (p1 ∨ p5))) → p1)) → (p3 ∨ p1)) → p5)) ∨ (False → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47644442404855713658137825803 : ((((((p5 → (False → (True ∨ (((p3 ∧ True) ∧ p5) ∨ p4)))) → ((((p5 → p3) → True) ∧ p4) ∨ p1)) → p5) ∧ p1) → (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49442328046288770358549408086 : ((((((p2 ∧ ((p1 ∧ True) ∧ (True ∨ p5))) ∨ (p5 ∨ False)) ∧ (p3 ∧ (p3 ∧ (True ∨ (p4 → p3))))) ∨ p5) → ((p3 → p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111102090961178027585218139117 : ((((((True ∧ p2) ∨ (p3 → (p2 ∧ p3))) → (p1 ∨ p2)) ∧ ((((((p1 → p2) → False) → p4) → p1) → p2) ∧ True)) ∧ True) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619197946923938429234146541365 : (((((p1 → (False ∧ True)) ∨ (((p5 ∨ (p5 → ((p5 → (False ∧ True)) → (p2 ∨ (p1 ∧ ((p2 ∧ p1) ∨ p2)))))) ∧ True) ∨ p1)) ∨ p1) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613284571585033925677740256946 : (((((((p1 ∨ False) ∨ (p4 ∧ True)) ∧ ((p1 ∧ (p2 → p5)) ∨ ((p5 ∨ p5) ∨ (p5 ∨ ((p3 ∧ p3) → True))))) → (p3 ∧ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_105954985221572673311655494713 : ((((True ∨ p1) → (p2 ∨ ((p1 → (p4 → ((True → False) ∧ p2))) ∧ p3))) ∨ ((p2 ∧ (p3 → (p4 → True))) ∨ (p5 → p5))) ∧ (False → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45512141296556837781533340847 : (((p1 ∨ (((p5 ∧ ((p5 → (p5 ∧ (((((p3 ∨ p4) ∧ (False → p5)) ∧ p4) ∧ p1) ∧ p5))) → False)) → p4) ∧ (p5 → p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383873521212731619105240509179 : ((((((((p3 ∧ p2) → (p3 ∧ ((False ∧ ((p1 ∧ p1) ∧ (p3 ∧ (p4 → p3)))) ∨ p4))) ∨ ((p2 ∨ True) → False)) → p2) → p3) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_44263344956810788473889328132 : (((((p4 ∧ ((p2 ∧ ((True → p5) → p4)) ∨ False)) ∧ (p3 → ((False ∨ p1) → (p2 → p1)))) → (((False → p1) ∨ p2) ∧ p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65703230678403771161436637399 : ((p4 ∨ ((((False → ((p1 → (p3 ∨ p1)) ∧ False)) ∨ (((p4 ∧ (p3 → (p3 ∨ p2))) ∧ p3) → p1)) → (True ∧ p2)) ∧ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230677343069000938086209105809 : (((p3 → p5) ∧ p5) → ((((p4 → False) → ((((p2 ∧ p5) → (p3 ∨ ((p5 ∧ p2) ∨ p4))) → p2) → (p5 → p3))) ∨ (p5 ∨ p1)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118717571477024704546891288109 : ((p5 ∨ ((p2 → (((((p3 → False) ∧ False) ∧ p4) ∨ p4) ∧ (p3 ∨ (p4 ∨ (p3 → (p1 → (False → p2))))))) ∨ (p5 ∨ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42593579488385931686375923907 : (((p2 ∨ (False ∧ ((((((False ∧ p5) → p4) → p1) ∧ p3) → p2) ∧ ((p2 ∧ (((p3 → p5) ∧ (p1 → False)) → True)) ∨ p1)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777798540648561745070508134041 : (((p1 ∨ ((p5 → (False ∨ ((True ∧ False) → p1))) → (((p2 → (False → (True ∧ True))) → ((p5 ∨ (p2 ∨ (True → p4))) ∨ p2)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213192519432610418987988159227 : ((((p4 ∨ p5) ∨ p5) ∧ p3) ∨ ((True ∧ ((p2 ∨ (p3 → p2)) ∨ (p4 ∧ p5))) ∨ ((True ∨ (((False ∧ (p1 ∧ p4)) ∧ p2) → p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_313254068542493092766583112015 : (p3 ∨ (((True → p5) → ((p5 → (((p4 → ((p4 → ((p1 → (p2 ∧ p1)) → ((False ∨ p1) → p3))) ∨ p3)) → p1) ∨ False)) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643770892190708075510259213006 : ((((p5 ∧ ((((p2 → ((p3 ∨ (p3 → (False ∨ p5))) ∨ p2)) ∧ p3) ∨ p2) ∧ (p4 ∨ ((p5 ∨ ((p1 ∨ p2) ∨ p2)) → p3)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148167766898286514766031209110 : (((((((p2 → p1) ∧ ((p5 ∨ True) ∨ ((p1 ∨ False) ∧ p3))) → False) ∧ p4) ∨ p1) ∧ ((p2 ∨ p3) ∨ p1)) ∨ (((False ∨ p4) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180960475867407774390795751614 : (((True → p3) ∧ ((((False → ((p3 → p3) ∨ False)) → False) ∧ p3) ∧ p3)) → ((p1 ∨ (((p1 ∨ p1) → p3) → True)) ∧ (p4 ∧ (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (False → ((p3 → p3) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h17 := h13 h15
  -- False on the left can always be used.
  apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h25 : (False → ((p3 → p3) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h26
    -- False on the left can always be used.
    apply False.elim h26
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h27 := h23 h25
  -- False on the left can always be used.
  apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704388786775905798213686251268 : ((((((p3 ∧ True) → p3) ∧ (True ∨ ((p5 → False) → p2))) → ((True ∨ ((((p1 ∧ p4) → ((p4 ∨ p4) ∨ False)) → False) ∧ p2)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147884811199814957134863021118 : ((((((p3 ∨ p5) ∧ (p5 ∧ (False ∧ (p4 ∨ (p4 → (p3 → False)))))) ∧ (True ∧ True)) ∧ p2) ∧ (p3 ∧ p2)) ∨ (p1 ∨ (p1 → (p5 ∨ p1)))) := by
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
theorem thm_5_vars_55531923360247641368501836235 : ((((p4 ∨ p2) → (p3 → (True ∧ p4))) → ((p4 ∨ ((False ∨ (False → False)) → ((p4 → p2) → (p2 ∧ ((p2 ∧ True) ∨ False))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116521968889201310401643419078 : (((p5 ∧ p3) ∧ ((p4 → (((p5 → (p4 → p3)) ∧ ((p1 ∧ p1) ∧ ((p2 → (p4 ∨ p3)) ∨ p3))) ∧ p2)) → (False ∧ p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177635315104833608878485791306 : ((((((p3 ∨ p3) → p2) ∧ (((p3 → p1) ∨ p2) ∧ True)) ∧ True) ∧ p5) ∨ ((p2 → (p3 ∧ (False ∧ True))) ∨ (p2 ∨ ((False → p1) ∨ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121366837013281709064973414390 : (((((p1 ∨ (((((p2 ∧ ((((p5 → p2) ∧ p1) ∨ p5) ∨ p5)) ∨ p5) ∧ p4) ∨ p3) ∨ (p5 ∧ p2))) ∨ p4) ∨ p1) → p5) → (p3 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ (((((p2 ∧ ((((p5 → p2) ∧ p1) ∨ p5) ∨ p5)) ∨ p5) ∧ p4) ∨ p3) ∨ (p5 ∧ p2))) ∨ p4) ∨ p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56436151924446562978306632469 : ((((p5 → True) ∧ (False → True)) → (((True ∧ False) ∨ p5) ∨ ((((p4 ∧ p1) → p2) ∧ (False → (False ∨ (False ∧ (True ∧ p1))))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205023107382938571779892620665 : (((p3 ∨ ((p4 ∨ p4) → True)) → False) ∨ ((((((True ∨ p4) ∨ p3) → True) ∨ p2) ∧ (p5 ∧ p4)) → ((((p4 → p4) → p5) ∧ p5) ∨ p2))) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790511492364614211090434723034 : (((p5 ∨ (False ∨ (p5 → (p1 ∧ (((p3 ∧ (((p2 ∧ p3) ∧ (p5 ∨ p5)) → p3)) ∨ (p1 ∧ ((True ∧ (True → p3)) ∧ p2))) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112177222037938864841512924495 : (((p4 ∧ ((p5 → (p5 ∧ (p2 ∨ ((p4 ∨ p2) ∧ (((p5 ∧ p5) ∨ p2) ∨ (p1 → p3)))))) → ((p3 → p2) → p3))) ∨ p3) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98797080870764736000110202401 : ((True → (((((p1 ∨ p3) ∨ ((p5 → (False ∧ ((p5 ∧ ((((p2 → False) → True) → True) ∧ p1)) ∨ p4))) → p3)) ∨ True) ∨ p1) ∧ p5)) → p5) := by
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
theorem thm_5_vars_790579612828692537163099980886 : (((p5 ∨ (p2 ∨ (True ∧ (((p1 ∧ p1) ∨ ((False → p3) → p3)) ∨ ((p2 → (False → True)) → ((p1 ∨ (p2 → True)) ∨ (True → False))))))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353909281967718876971639152384 : (p4 → (p2 → ((p1 ∧ ((p1 ∧ ((p1 ∧ (p3 → p1)) → p3)) → (((False → p2) ∧ (True ∨ (p2 ∨ (True ∧ p2)))) → p5))) ∨ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134629835308743104650701194996 : ((((True ∨ (((p1 ∨ ((p5 ∨ False) ∨ (p4 → p5))) → (p4 ∧ p3)) ∧ p3)) ∧ ((p2 ∧ p5) → (p1 ∧ p2))) → p2) ∨ ((p2 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306004092223684375026020160289 : (p1 ∨ (((p2 ∨ p4) ∨ (p2 ∧ p5)) ∨ (True → (p5 ∨ (False ∨ (p1 → ((p2 → ((((p4 ∨ (p4 ∨ p3)) ∨ p2) ∨ p1) → p2)) ∧ True))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57574438034611971402363969402 : ((((p2 ∨ True) ∧ p4) → (((((p5 ∨ p5) → (False ∧ (p5 → (p2 → ((p2 → p2) ∨ p4))))) → False) ∧ p5) ∧ ((False ∧ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192360693346581799380203700559 : (((p1 → (p5 → (True ∨ (p3 ∧ (p2 → True))))) ∧ True) → ((p3 → ((p3 ∧ p4) ∧ (p1 ∧ p1))) ∨ ((False → p3) ∧ (p3 → (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824357106447411257367140241517 : ((((((True → p1) ∧ True) ∧ (((p3 → False) ∨ (p4 ∧ (((p3 ∧ (p5 ∨ (p3 ∨ (p1 → p2)))) → p4) ∧ p5))) ∨ (False ∧ p5))) ∧ p2) → p1) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329679466211224083848526698378 : (True → ((p1 ∨ p5) → (((((((p5 → p3) ∨ True) → (False → (p2 ∧ p3))) → p5) → p3) → ((p2 ∧ False) ∨ (False → (False ∨ p2)))) ∨ p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638164827781047704070476346769 : ((((((p3 → (True ∧ (p4 → (True ∨ False)))) → p4) → ((p3 ∧ ((p3 → p4) → True)) ∨ (((False → (True ∨ True)) ∨ p4) ∧ p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1797862746122129188179446125 : (((p1 ∧ (p5 ∧ p3)) ∨ (((False → p1) → (((p3 → (((p4 ∧ False) → p5) ∧ p2)) ∧ True) → p3)) ∧ p4)) ∨ (p5 → (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147986005146875783942228447030 : (((((p2 ∧ (p5 ∧ (((((True ∧ p3) ∨ p2) → p2) ∧ (False ∨ p4)) → False))) ∨ True) ∨ p4) ∨ (p4 ∧ p3)) ∨ (p3 → ((p3 ∨ p5) ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



