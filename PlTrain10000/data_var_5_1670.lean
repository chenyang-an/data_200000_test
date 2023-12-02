variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342768012252615478652643945173 : (p2 → ((p1 ∨ (p3 ∨ (((p4 ∨ False) ∨ p3) → False))) ∨ (((p3 → p4) ∨ (p3 ∨ ((True ∨ p1) ∧ (p5 ∧ p5)))) ∨ ((p1 ∧ p1) → True)))) := by
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
theorem thm_5_vars_246044426034820033731185388404 : ((p4 ∧ False) ∨ ((p3 ∧ p3) ∨ ((p4 ∧ (p1 → (((p4 → p2) ∧ (False ∨ p1)) ∨ (p5 → ((((p2 ∧ p3) ∨ p3) → False) ∧ p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781936170014509824298469987544 : (((p2 ∨ (p2 → (p1 → ((p5 ∨ ((((p4 → False) ∧ (False ∨ p3)) ∨ ((True → False) → ((True ∨ p2) → p5))) ∨ p2)) ∨ (p3 → p5))))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118708768794694270834696609166 : ((p5 ∨ ((p1 ∧ ((True → p5) ∧ (((p4 ∧ (((((False ∧ p1) ∨ False) ∨ p1) ∨ False) ∧ (p1 ∧ p1))) ∨ p4) → p5))) → p5)) ∨ (p5 ∨ p2)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149210104583545347867919545565 : (((False ∧ False) ∨ (False ∧ ((p2 → ((True ∧ (p2 → True)) ∧ p4)) → (((p5 ∨ True) → (p4 ∧ p5)) ∨ p3)))) ∨ ((False ∧ (p4 ∧ p2)) → False)) := by
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
theorem thm_5_vars_171932806808445331770031356425 : (((((p1 ∧ p3) ∨ (((p4 ∨ True) → (p5 → True)) ∨ p3)) ∨ p3) ∧ (p3 → p4)) ∨ (((p3 ∧ p4) ∨ p3) ∨ (p4 ∨ (p2 ∨ (True ∨ True))))) := by
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
theorem thm_5_vars_166634407714985398098070607680 : ((p1 → ((((p5 → p4) ∨ ((False ∧ p3) ∨ (p1 ∨ p5))) → ((p2 ∨ p4) → False)) ∧ False)) ∨ (p2 → (True ∧ (False → (False ∨ (p4 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260512098379411714298057172289 : ((p3 → False) → (p5 ∨ (p1 → (p3 → (((p2 ∧ True) → ((p4 ∧ False) ∧ (((p1 ∧ p5) ∧ p4) ∨ p5))) ∧ (p2 ∧ (p5 → (p5 ∨ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h4.left
  let h14 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114523741172527824946194779697 : (((p5 ∧ (((p2 ∨ (p1 → ((p3 ∧ True) → (p2 → (False ∧ True))))) ∨ (p4 ∧ p4)) → False)) → ((True ∧ (p3 ∧ False)) ∨ p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760270762424651955861546875139 : (((p2 ∧ ((p5 ∧ p5) ∨ ((True → (((p2 ∧ (p4 ∨ (False ∨ p1))) ∧ ((False ∨ (p1 ∧ (True → p3))) ∧ p4)) ∧ (False → p2))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254791576816674724145959854527 : ((p3 ∧ p4) → ((p3 ∨ p1) → (((((((True ∧ p5) ∨ p1) → (p5 ∧ (p2 ∧ True))) → p1) ∨ (p4 ∨ ((p3 → p2) → False))) ∨ p3) ∧ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254155138239367911288468699814 : ((p2 ∧ p1) → (((p3 → (p1 ∨ (((p5 ∧ p2) ∨ p5) → ((True ∧ p4) ∨ p4)))) → ((p5 ∨ False) ∧ ((p5 ∨ (p4 → True)) ∧ False))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → (p1 ∨ (((p5 ∧ p2) ∨ p5) → ((True ∧ p4) ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179477049509614733685782126040 : ((True → ((((p5 → p5) → False) ∨ (True ∨ (p4 → False))) ∧ (p5 ∨ p3))) ∨ (p2 → (((False ∨ (p5 ∧ p2)) ∨ ((p3 → p3) ∨ p3)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199529842709277941141503499469 : (((((p5 ∧ (p5 → p2)) ∨ p5) ∧ p1) → p2) → (p2 ∨ ((p2 → p5) ∨ (False → ((False ∧ True) ∨ (((p3 ∨ (True ∨ p4)) → p1) → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178624068439021762861668183040 : (((((p5 → (p2 → p3)) ∨ p2) → True) → (((False ∨ False) ∧ p3) ∧ p3)) ∨ (p3 ∨ (((p3 → ((p4 → p3) ∨ False)) ∨ (False ∧ p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178093255437264132340989021237 : ((((False ∨ (p5 ∧ (((p4 ∧ p3) ∨ p5) ∨ (p5 → p3)))) → p1) → p4) ∨ (True ∨ ((p5 → (True ∨ (p3 → (p4 ∨ p4)))) ∧ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190166570762838062668592794750 : (((p1 ∧ ((p2 ∨ False) → (p4 ∧ (False ∨ p2)))) ∧ False) ∨ (p1 ∨ (p2 → (((p2 → ((False ∨ p1) ∧ (True → (True → False)))) ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_323520055904285847914662196595 : (p5 ∨ ((p5 ∧ ((p1 → ((((p4 ∧ (((p3 ∧ False) ∧ p1) → p3)) ∧ p3) ∧ p5) ∨ (p3 → p1))) → (p1 → p5))) ∨ ((False → p2) ∨ p4))) := by
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
theorem thm_5_vars_14712883914030014063657117567 : ((((p3 → (p5 ∨ (p2 ∧ ((((p1 ∨ True) ∨ p3) ∨ ((p4 ∨ (False → True)) ∨ (p1 ∨ p2))) ∨ p1)))) ∨ (p2 ∨ True)) ∨ (False → p3)) ∧ True) := by
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
theorem thm_5_vars_113366745414445088439449676128 : (((False ∨ ((((p4 → p5) ∨ ((p5 ∨ (False ∨ p3)) ∨ p3)) → (p4 ∧ ((p2 ∧ p3) ∨ (p1 → True)))) ∧ True)) ∧ (p3 → p3)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139922501016734628050740488577 : (((((p3 → False) ∨ ((True ∨ (p1 ∧ p1)) ∨ p2)) ∧ (p2 ∧ (((p5 ∧ p2) ∨ (p1 → p1)) → p3))) ∧ (True → p5)) → (p3 → (p5 ∨ p4))) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h17
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h6.left
        let h23 := h6.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h6.left
      let h28 := h6.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h30 := h4 h29
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55096555185276965433530888018 : (((p3 → (False ∧ (p3 ∧ (p3 ∧ True)))) ∧ (((p4 ∧ (((p3 ∧ p2) → ((True → p2) ∨ p4)) → (p5 ∨ p5))) ∨ (p5 ∧ p3)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725256536419733221586332086080 : ((((p3 → (False ∧ True)) ∧ (((((True → p1) ∧ ((((True → True) → (p5 ∧ ((p3 ∨ True) → p4))) → True) ∨ p5)) → p1) ∨ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180519199213592285210893238194 : ((((True ∨ (((p1 ∧ p4) ∧ False) ∨ p5)) ∧ p1) ∨ (p5 ∧ (True ∧ p2))) → ((((p4 → (p3 ∨ (True ∨ True))) → p3) ∨ p1) ∨ (p2 ∧ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h17
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52689929893795350189742318894 : (((True → (((True → (True ∨ True)) ∧ True) → (((p3 → p1) ∧ p4) → p5))) ∨ (False → (((((p1 ∨ p5) ∧ False) ∨ p3) ∧ True) ∧ p5))) ∨ p3) := by
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
theorem thm_5_vars_140935423015617152303854630129 : (((((p2 → (p5 ∨ (False → (p2 ∨ True)))) → p3) ∨ p2) ∨ ((True ∨ (True ∧ (True ∨ (p1 ∨ False)))) → (False ∧ p2))) → ((p4 ∧ False) ∨ True)) := by
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
theorem thm_5_vars_336954287549641661513560599515 : (p1 → (((p3 ∧ (((p3 ∨ p4) ∧ (((p4 ∨ p5) ∧ ((p3 → p1) ∨ ((p4 ∨ False) ∧ p3))) ∨ p5)) ∨ p5)) ∨ (p4 → p1)) ∧ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112458408301211849927158319197 : ((((((p1 ∨ p1) ∨ (((False → (p3 ∧ True)) ∧ (p3 ∨ (True → False))) → p4)) ∧ ((True ∨ p3) → (p2 → p4))) ∨ p1) → p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204702653919439185248105370086 : (((p4 ∨ ((p5 → True) → p1)) ∨ p2) ∨ (p5 → ((((p5 ∨ (p5 → (p2 ∧ p1))) ∨ p2) ∧ (False → p5)) ∧ (((p4 ∨ p1) ∧ p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218113400883478386467788337369 : (((p1 → p4) ∧ (False → p1)) → (((True → (False ∨ (((False → p5) ∧ True) → ((p1 ∨ p3) ∧ p4)))) ∨ p1) ∨ (True ∨ (False → (p4 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149116880689821217815650196622 : (((False ∧ p1) ∧ ((p3 ∧ ((p5 ∨ ((p5 ∨ False) → (((p1 → (p4 ∧ p4)) ∨ False) → True))) → p4)) ∧ p5)) ∨ (((p2 ∧ p4) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117591827414479605675832420909 : ((p2 ∧ (p4 ∧ (p2 ∨ (p4 → ((((p5 ∧ p3) ∨ True) → (p1 ∨ ((p3 ∧ p1) → ((p4 → p1) ∧ p5)))) ∨ (True ∨ p1)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357399532642060104509516309378 : (p5 → ((p5 ∧ p3) → (((p5 ∧ (p4 ∧ ((p4 → p3) → p3))) ∧ (p5 → ((True ∧ p2) → False))) → ((p3 ∧ (p5 → (p1 ∧ p1))) ∨ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136612944603797437508254005326 : (((p5 → (p4 ∨ p2)) ∨ ((p4 → False) → (p4 → (p2 ∧ (p5 ∨ ((p5 → (p3 ∧ ((p1 → p2) ∧ p2))) → False)))))) ∨ ((p1 ∨ p3) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342591476129612914465887347469 : (p2 → ((((p3 ∨ p5) ∨ ((p5 ∧ p2) → ((p1 ∧ p3) ∧ True))) ∧ p5) → ((((p3 ∧ False) ∨ True) ∧ ((False ∧ p1) → (False ∨ True))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41092410534351033649261926225 : ((((((p2 → ((p4 ∨ (((p4 ∧ True) → ((p2 → False) ∨ p2)) ∧ p3)) ∨ p3)) ∨ False) ∧ (False ∧ p2)) ∧ (p3 ∧ (True ∨ p3))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52302674871825550281825323223 : (((((p3 ∧ p5) ∨ (p1 ∧ ((p1 ∨ (p2 → (p3 → p3))) → p2))) ∧ p5) ∧ (((True ∧ (p2 ∨ (p4 ∧ (p3 ∨ p3)))) ∨ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866430455969119936691866692 : ((p4 ∨ (p1 → (((((((True ∧ True) ∧ (p2 → p5)) ∨ p1) ∨ (p3 → False)) → p5) ∨ p2) ∧ (((p3 → True) → p5) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42252257006147802486366543616 : (((p1 ∧ ((False ∧ (((((False → ((p4 ∨ p2) ∨ p4)) ∧ False) ∨ (p4 ∧ False)) ∧ ((p1 → p5) → p1)) ∨ (p1 → p4))) ∧ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49128914283611274924649494643 : (((((p5 ∧ p2) ∨ ((((p1 → p4) ∨ (p3 ∧ True)) ∨ p3) ∨ False)) ∨ ((True → (p3 ∨ True)) ∨ (p2 ∨ p4))) ∨ ((p1 → False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149651628334452252267534791418 : ((p4 ∧ ((p5 ∨ (p4 ∧ (p2 → True))) ∨ (((False ∧ p4) → p3) ∧ ((True → p2) ∧ ((p4 ∧ p5) ∨ p4))))) ∨ (p5 ∨ ((p4 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654927269097261087152068689062 : (((((((((p1 → p3) ∧ True) → p1) ∨ True) ∧ ((p1 → p1) → ((((p4 ∨ True) ∨ p2) ∧ False) ∧ (p1 ∧ p1)))) → p4) ∨ (True → p5)) ∨ p1) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60963822313396890041084894838 : ((False ∧ ((((p2 ∨ (p5 ∨ (p4 ∨ p2))) ∨ ((p4 ∨ p1) → False)) ∧ (p5 ∨ ((p5 ∧ (p2 ∨ (p4 → p1))) → (True → p3)))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258784338872163587566508638240 : ((True → False) → (((((p2 ∧ (p5 → p4)) ∨ (False ∧ p5)) ∨ (p3 → (p3 → p4))) ∧ p2) ∧ ((p5 → ((p3 ∧ p1) ∧ p4)) ∨ (p1 ∨ p5)))) := by
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
theorem thm_5_vars_681684577981215113097245882443 : ((((p4 → (p2 ∧ (True ∨ (p4 → (((True ∨ p3) ∨ ((p5 → p5) → p5)) ∨ (p1 → (p3 ∧ p5))))))) → (((p3 ∧ True) → p1) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_147640355103559114879509737588 : ((((p1 ∧ ((p2 ∨ ((True ∧ (p3 ∨ ((False → (False → (p3 ∧ p3))) ∨ p4))) → p3)) → p3)) → p4) → False) ∨ (p1 ∨ ((p2 → True) ∨ p4))) := by
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
theorem thm_5_vars_352639090046368251077479127854 : (p4 → ((p2 ∧ False) ∨ (((((p3 ∨ p1) ∨ p5) ∨ p4) ∨ (((p3 → p4) ∨ ((True ∧ p1) ∨ True)) ∨ False)) ∨ (p5 ∨ ((True ∧ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684085695976452518433481995324 : (((((((p2 ∨ ((p2 ∨ ((p2 ∨ p3) ∨ p4)) → (p4 ∧ False))) ∨ p4) ∧ True) ∧ (p4 ∧ p5)) ∨ ((False ∨ (p3 ∨ p5)) ∨ (p4 → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_818686629561197881062556463437 : (((((((((True ∨ p4) → ((((p1 ∨ p4) ∨ (True ∧ (p1 ∨ (False ∨ p3)))) → p1) ∧ p1)) → p3) ∨ True) ∧ p2) → (True → p1)) ∧ p2) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ p4) → ((((p1 ∨ p4) ∨ (True ∧ (p1 ∨ (False ∨ p3)))) → p1) ∧ p1)) → p3) ∨ True) ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117107649358202787860653584378 : (((p2 → p4) → ((((p2 → (p3 ∨ ((True → p1) ∨ p5))) ∨ ((p4 ∨ p1) ∧ p2)) → (p2 ∨ (p3 ∨ p1))) → (p4 ∧ p5))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46531299119734561358276447201 : ((((p5 ∧ p1) ∨ ((((((p1 ∨ (((p1 ∨ p2) → p3) ∧ (p4 ∧ p5))) ∨ False) ∧ True) ∨ False) ∨ p4) ∧ (False ∨ False))) ∧ (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191233293353350861943339111061 : (((p1 → (p2 ∨ p3)) → (((p5 ∨ p4) → p2) → p1)) ∨ (False → (((True ∧ (False → (p2 ∧ (p3 ∧ (p3 ∧ (p2 → False)))))) ∧ p3) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317818240680117120157146245264 : (p4 ∨ (((p3 ∧ ((p2 ∨ p4) ∧ p5)) ∧ ((p5 → (True ∨ ((p4 → p5) ∨ (p3 → ((p2 ∨ (p2 → p1)) → (True → p3)))))) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117808290445233590359952473042 : ((p4 ∧ (((p3 ∧ True) → p1) → (((p2 → p2) → ((p4 ∧ p3) → False)) ∧ ((p3 ∨ ((p1 ∧ p4) ∧ False)) → (True → p2))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675049458794750723271704412541 : (((((p5 ∨ (((((((p4 ∨ (p4 ∨ (p5 ∨ p5))) → True) ∧ True) → p5) ∧ p3) ∨ p4) ∨ p5)) ∧ p2) ∧ (((p3 → False) ∨ p4) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122794603512934853431053227243 : (((p5 → (((False ∧ (p2 ∨ p5)) ∧ ((p3 ∧ p1) ∧ ((p3 ∨ (((p3 ∨ p5) → p3) ∨ p4)) ∧ p4))) ∨ p5)) → (True ∧ False)) → (p2 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (((False ∧ (p2 ∨ p5)) ∧ ((p3 ∧ p1) ∧ ((p3 ∨ (((p3 ∨ p5) → p3) ∨ p4)) ∧ p4))) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64801314493183802896632969720 : ((p2 ∨ ((p3 ∧ (p1 ∨ (p2 ∨ ((p5 ∧ p5) → ((True ∧ ((p5 ∨ ((p2 ∨ p5) → (p5 → (False ∧ p4)))) → p3)) ∨ p3))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226368534561236108147350359241 : (((True → p2) ∨ p3) ∨ ((p2 ∧ ((((p1 ∧ (p3 ∨ False)) ∨ p5) → (((True ∨ (p5 ∧ (True ∨ p2))) ∧ False) ∨ (p1 ∨ False))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110725528663848384933732418820 : (((((((False → p1) ∨ ((p1 ∧ p5) ∧ (((p1 ∨ p3) → p4) ∧ p4))) → (False ∧ True)) ∨ (p4 ∨ (False → p5))) ∧ p2) ∧ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_857111319149829160811531545912 : (((((p4 ∨ ((p3 ∨ ((p5 ∨ (True ∧ p3)) ∨ (((p4 → False) ∧ p1) ∧ (p4 → (p5 ∧ True))))) → (False ∧ (False → p1)))) ∨ True) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((p3 ∨ ((p5 ∨ (True ∧ p3)) ∨ (((p4 → False) ∧ p1) ∧ (p4 → (p5 ∧ True))))) → (False ∧ (False → p1)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194229783225875042001580013412 : ((p4 → ((((False ∨ (p5 ∧ True)) ∧ p2) → False) ∨ p3)) → ((((p2 ∧ (p2 → True)) → p3) ∧ ((((True ∧ p4) ∧ p5) → p5) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113137395859648621310741684002 : (((p2 → (((True ∨ ((p2 → True) ∧ p2)) → p5) ∧ (p4 ∨ ((p1 ∨ (p2 → p2)) ∧ ((p5 ∨ p4) ∨ (p3 → p1)))))) → False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147243558467348182050803677255 : ((((((p3 ∨ (p2 → (p5 ∨ p5))) ∨ True) ∧ (p1 ∧ (((p1 ∨ False) ∨ (False ∨ False)) ∧ p3))) ∧ p1) ∨ p2) ∨ ((True ∨ p2) ∨ (False ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117673790117313944857517639773 : ((p3 ∧ (((p2 ∧ (p5 ∨ p3)) ∧ ((p4 ∨ p2) ∨ (True → True))) ∧ ((False ∧ (True ∨ p2)) ∨ ((p4 → (p1 ∨ p2)) ∨ p5)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354711775065887416595182025308 : (p5 → ((((p1 ∨ ((((False ∨ (p5 ∧ p1)) ∨ p5) → p2) → p1)) ∨ ((True ∨ (p4 → p2)) ∨ (p4 → p1))) ∧ (True ∨ (True ∧ False))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306401725869804618920828178707 : (p1 ∨ ((False ∧ p5) ∨ (p1 ∨ (((((((p1 ∧ p1) ∨ (p5 ∨ p5)) ∨ False) ∧ p5) ∧ (p3 ∧ p5)) ∧ (((True ∧ p5) ∧ p2) → p3)) ∨ True)))) := by
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
theorem thm_5_vars_354957035380013203353484491581 : (p5 → ((p1 → (((((((False → p4) ∧ p1) ∨ True) ∧ p3) ∨ False) ∧ (((p3 ∧ True) ∨ False) ∨ p2)) ∨ (((p1 ∨ True) → True) ∧ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47233835726557546576203402432 : (((((True → p4) → ((False → (p3 ∨ False)) → p3)) ∨ ((p5 → ((p1 ∨ (p4 → False)) ∨ p5)) ∨ (p4 → (True ∨ p5)))) ∨ (p5 ∨ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_247763127631594786914482209408 : ((p1 ∨ False) ∨ (p4 → (((p1 → p1) → ((p4 → ((False → (((p4 ∨ (p4 ∧ (True ∧ p4))) → (False ∧ p3)) → False)) ∨ p5)) ∧ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134619497657486846771678215996 : ((((((p1 → (p3 ∨ p4)) ∨ ((True ∨ (p3 → (p5 → p1))) → (p1 → False))) ∨ p2) → ((False ∨ p4) ∧ p1)) → p5) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324717459464183967803772384647 : (p5 ∨ (((True → p5) ∨ p4) → ((((p3 ∧ p3) ∧ (p3 → (False ∧ (p2 → p1)))) → (p2 ∧ False)) ∨ (p3 ∧ (p3 ∨ (p3 ∨ (p4 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h24 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h25 := h21 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26
    -- Conjunctions on the left can always be decomposed.
    let h27 := h19.left
    let h28 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h31 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h32 := h28 h31
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44553242289544536219530656438 : (((((p5 → ((p2 ∨ True) ∧ (True → p4))) ∨ True) ∧ (p4 ∧ ((True ∨ ((p4 ∨ (p5 → p2)) ∧ True)) ∧ ((False → True) ∧ True)))) → p4) ∨ p3) := by
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
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h8.left
        let h17 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h8.left
        let h20 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h25.left
        let h34 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h25.left
        let h37 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609931588067328426064881479078 : (((((p4 → ((((((True ∧ p3) ∧ p2) → True) ∨ p3) ∨ ((False ∨ p3) ∨ (False → (p2 ∨ True)))) → (p4 → (p4 ∧ False)))) ∨ p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54002808958522012795791572510 : (((((p1 ∨ ((p2 ∧ (False ∧ False)) ∨ True)) ∨ p3) → False) → (False ∧ (((True → (p1 ∧ (p5 ∧ p2))) ∨ (p5 ∧ (p2 ∧ p5))) ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ ((p2 ∧ (False ∧ False)) ∨ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∨ ((p2 ∧ (False ∧ False)) ∨ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ ((p2 ∧ (False ∧ False)) ∨ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186647058063973990403300883355 : ((((((False ∨ p4) ∨ p5) ∨ p5) ∧ True) ∧ ((p1 → p3) → p4)) → (True ∧ (p1 ∨ (p5 ∨ (p2 → ((p1 ∧ p5) → ((p1 ∧ False) ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159266753922055641829373846284 : ((p4 → ((p5 ∧ (((p5 ∨ ((True ∨ True) ∧ (True ∨ ((p5 ∨ True) → False)))) → False) ∨ p1)) ∧ p3)) ∨ (p4 → ((p1 → (p3 ∨ p4)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643291363748751757171708195697 : ((((p3 ∧ (True ∧ ((((((p3 ∨ (p1 ∨ (p3 ∨ p4))) → p3) ∨ (((p1 → p1) ∨ p2) ∧ p2)) → p1) → p3) → (False → p3)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56342006154208235582647041012 : (((((p4 → False) ∨ p5) ∨ p1) → ((p4 ∧ p2) ∨ ((p4 ∧ (True → p3)) ∧ (p5 ∧ (p3 ∨ (p2 ∧ (p2 ∨ (p2 ∨ (p1 → p3))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804702978367040062667139087396 : (((p3 → ((True ∨ (True ∧ p3)) ∧ (((((p3 ∨ p2) ∧ ((p3 ∨ (False ∨ (p2 → p5))) ∨ False)) ∧ p3) ∧ False) ∨ ((p1 ∧ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54517000159830536980773133411 : ((((p2 ∧ p3) ∧ (((p4 ∨ p2) ∧ False) ∧ False)) ∨ (((p3 → ((p2 ∨ p1) → p2)) ∨ ((((p1 → p5) ∨ p4) ∨ True) → p2)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58315289691348741373823804324 : (((False ∨ True) ∧ ((((p3 ∧ (((p1 → p4) ∧ (True ∧ (True ∨ False))) ∨ (p3 ∧ True))) ∨ (p2 ∨ p1)) ∨ (True ∧ (p5 → p2))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199183446930169491675719704280 : (((p2 ∧ ((p4 ∨ p2) ∨ (False ∨ p5))) ∧ p3) → ((((True ∨ p5) ∨ p4) ∨ p1) → ((p3 → (False ∨ p5)) → ((p1 ∧ p1) ∨ (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h1.left
        let h8 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- One of the premise coincides with the conclusion.
            exact h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h33
            -- One of the premise coincides with the conclusion.
            exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h1.left
      let h36 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h41
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h43
          -- One of the premise coincides with the conclusion.
          exact h43
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- False on the left can always be used.
          apply False.elim h45
        case inr h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h47
          -- One of the premise coincides with the conclusion.
          exact h47
  case inr h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h1.left
    let h50 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h49.left
    let h52 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h54 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h48
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h55 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h48
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- False on the left can always be used.
        apply False.elim h57
      case inr h58 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h48
        -- One of the premise coincides with the conclusion.
        exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308749498515236529838542639017 : (p2 ∨ ((p5 → (((True → (True ∧ (p4 ∨ (p2 → p2)))) ∧ (p5 ∧ p2)) ∨ (((True → (((True ∧ False) ∧ False) ∨ True)) ∨ p1) ∨ p4))) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346284965945093864215461260404 : (p3 → (((((p5 → False) → (((True ∨ (True → p4)) → True) → (p4 ∨ p4))) ∨ ((p1 ∧ (p2 ∧ p4)) → (p3 → p3))) ∧ p3) ∨ (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55584923959740269168892571425 : (((p2 ∨ (p1 ∨ (p3 ∨ (p2 ∨ p2)))) → (((p3 → (p1 ∨ (p1 → p4))) ∨ (p4 ∨ p1)) → (p3 → (p1 ∧ ((False ∧ p2) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187030207259255208420869407673 : (((p3 → (p3 ∨ False)) → ((p5 ∧ (p1 ∨ True)) → (p2 ∧ True))) → (p2 ∨ (((p4 ∨ ((p1 ∧ p2) → True)) ∨ ((p2 ∧ p2) → False)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54170287091609680504701400898 : (((((((True → True) ∧ p4) ∨ p5) → p3) ∧ p4) ∧ ((False ∨ ((p2 ∨ False) ∨ (((p4 → p2) ∨ p5) → (True ∧ (p5 ∧ p5))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234634880368258113501586437791 : ((p3 → (p2 → p3)) → (((False ∧ p5) ∨ p5) ∨ (((((((False ∨ True) ∨ (((p5 ∧ p2) ∨ p4) ∧ False)) ∧ p1) ∧ p2) ∨ p1) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45025859332003540316135224947 : ((((p1 ∨ True) ∨ (p3 → (((p4 ∨ (p4 ∨ p3)) → (p3 ∧ ((p4 ∨ p3) → p5))) ∧ (((p4 ∨ p5) ∨ (True ∨ True)) ∧ p2)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246041446880640109384641307478 : ((p4 ∧ False) ∨ ((p4 ∨ (p5 → p1)) ∨ ((((False → p2) → p3) ∧ (((True ∧ (p5 ∨ ((p2 ∧ True) ∨ p1))) ∧ (p2 → p2)) → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721770932593805004785807440536 : ((((p2 ∨ ((p3 → p5) ∧ p3)) → (p2 → ((((p3 ∧ ((p1 → False) ∨ p3)) ∧ (True ∨ p2)) → p4) ∨ (((p1 → False) ∨ p5) ∨ True)))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715564230059622673117224058285 : (((((p3 ∧ (p3 → p3)) ∧ p2) ∧ (p2 → ((p4 ∧ (((p5 → (p5 ∧ True)) → ((p1 ∨ False) ∨ p1)) ∧ (p5 ∧ p4))) ∨ (False ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111786219720045723503186080989 : (((((p5 ∧ ((((p5 ∨ p1) ∧ False) ∨ p2) → (False ∨ p1))) → (((p4 ∨ True) → (p3 ∨ p1)) ∧ p4)) ∨ (p4 → p1)) ∨ True) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135104901516110566863818513751 : (((((p3 ∧ p4) ∨ (p4 ∧ p2)) → ((p2 → False) → (((p1 → (False ∨ False)) ∨ (p2 → True)) ∧ True))) ∨ (p1 ∧ p5)) ∨ (p5 ∧ (p3 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42004182537055961040889429534 : ((((p2 → p3) ∧ (((True → (((((p4 ∨ p5) → True) ∨ p2) ∨ p3) → p1)) ∨ p1) → (((p3 ∧ (p5 → p4)) ∨ p2) ∨ p4))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59307996694440881495087428791 : (((p4 ∨ False) ∨ (((p2 ∧ (p3 → False)) ∨ p1) ∨ ((((p5 ∨ ((((False ∧ p3) ∧ p5) ∧ p1) → p3)) ∨ True) ∧ (False → p4)) → True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149379259640044171391478076950 : (((p3 → False) → (p1 ∨ ((p2 ∧ ((p2 → False) ∧ True)) ∨ (p3 → (p4 ∧ (p2 ∧ (p2 ∨ (p3 ∨ p1)))))))) ∨ (p1 ∨ (p1 ∨ (p4 ∨ p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685297488130976923108136434939 : ((((p2 → (((((p3 ∧ p1) ∧ p2) ∨ p1) ∧ False) ∨ ((False ∨ (p1 ∨ (p2 → p5))) ∧ False))) ∨ (((False ∧ p1) → (p1 ∧ p3)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_233230979883628728506282996393 : ((p5 ∧ (p4 → p5)) → (p2 → (((((((p1 → p3) → p2) ∨ p2) ∨ (p5 ∧ p5)) → p3) → False) → (p1 ∨ (((p3 ∨ p4) ∨ True) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
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
theorem thm_5_vars_352296406882271038454694415250 : (p4 → ((p3 ∨ (p3 ∨ (p2 → p5))) → (((((p4 → p4) ∨ (False ∨ ((p4 ∨ True) ∨ p5))) → (False ∨ p4)) ∨ p4) ∨ (p4 ∨ (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



