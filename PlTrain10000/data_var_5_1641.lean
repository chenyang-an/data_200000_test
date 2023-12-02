variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46909009552192652938599216439 : ((((((p1 ∧ (p2 ∨ ((p5 ∨ True) ∨ p2))) → (p4 ∨ ((p1 ∨ True) → p1))) ∧ ((False ∧ p2) ∧ (p2 ∨ True))) ∨ p3) ∨ (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46944581344169822104773513283 : ((((p3 ∨ (p1 ∨ (p5 ∨ (p5 → (p1 ∧ (p5 ∨ (p2 ∧ (((((False ∨ False) → p3) ∧ p2) ∨ p5) ∨ p4)))))))) ∨ p2) ∨ (False → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329500307759440298346232929499 : (True → ((p5 → True) ∧ (((p1 ∨ ((((False → p4) ∧ p3) ∧ (True → ((p1 → False) ∧ (((False ∧ p1) ∧ p4) ∧ p2)))) ∨ p4)) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327111016141693719860231986768 : (True → (((p4 ∨ p3) ∨ ((p5 ∨ (p2 ∧ ((p5 ∧ p2) → p4))) ∨ ((((True ∧ False) ∨ p1) ∨ p2) ∨ ((p5 → p5) ∨ (p5 ∨ True))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125535719084759661258922281532 : (((True → p2) ∧ (((True → ((((p4 ∧ p4) ∨ p2) ∨ p3) → (p3 ∧ (p1 ∧ p5)))) ∧ ((True → p4) ∧ True)) ∧ (p1 ∧ p2))) → (p5 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h6.left
  let h12 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h13
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : (((p4 ∧ p4) ∨ p2) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616042625745146670754266471588 : (((((True ∧ (((False → ((p1 ∧ p5) → p2)) ∧ ((p5 → p1) ∧ p5)) ∧ p5)) → (p2 ∨ ((p4 ∨ (True ∨ True)) ∧ (p1 ∧ p5)))) ∨ p4) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h11
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64055029948909239915988737249 : ((False ∨ ((p4 → (((p3 ∧ (((False → p3) → ((True → True) ∨ p1)) ∨ p4)) ∨ (p3 ∧ p4)) → p5)) ∧ ((p1 → (p2 → p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234286675178436925848612951177 : ((False → (p3 → p4)) → ((((p3 ∨ (p4 ∧ p3)) ∨ p2) ∨ (False → ((False ∨ (((False → True) ∧ p3) → p3)) → (p1 → (p4 ∨ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351010606330843627343258101171 : (p4 → ((True → ((((p2 → ((False ∨ p3) ∨ (p4 → (p5 ∧ p4)))) → p4) → (p1 ∧ (p2 → p3))) ∨ (False ∨ (p2 ∧ p2)))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217260515181240250950205604232 : (((p1 ∧ (p1 ∨ True)) ∨ p4) → ((((p2 ∨ (((False ∧ ((p3 ∧ p1) → True)) → (p4 → False)) ∧ True)) → True) ∧ ((p4 ∨ False) ∧ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84840189174914203489008924561 : (((True → (((p3 ∨ p4) ∧ (p4 ∨ (p4 ∧ (p3 ∧ (p2 ∧ p1))))) ∨ p3)) ∧ ((p2 ∨ (p1 → (p4 → (p1 → p3)))) → (True → False))) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
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
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h27 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h28 : (p2 ∨ (p1 → (p4 → (p1 → p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- Implications on the right can always be decomposed.
      intro h30
      -- Implications on the right can always be decomposed.
      intro h31
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h32 := h3 h28
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h34 := h32 h33
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60413092383109897058263346983 : (((p4 → p1) → (((((p2 ∨ ((p1 ∧ p5) → (p2 ∧ (p5 → (p4 ∨ p1))))) ∧ (p4 ∨ (False ∨ (p5 → p5)))) ∨ p1) ∨ p4) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118144714982767563295989553735 : ((False ∨ ((((((p2 → ((True ∨ p5) ∧ p5)) ∧ p4) → True) ∨ p1) ∧ True) → ((((p3 → True) → p1) ∧ p2) ∨ (False → p3)))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232295959131801495086963902654 : (((p3 → True) → p3) → (p4 → ((p3 ∧ p1) ∨ ((((p3 → p4) → False) ∨ p1) ∨ (p3 ∨ ((p4 ∧ p3) → (p3 ∧ ((p1 ∨ p5) → p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754194637278828479763058559418 : (((False ∧ (((p4 → p4) → p1) → (((p1 ∧ ((p1 ∨ (False ∧ False)) → p4)) ∨ p5) ∨ (p2 → ((p2 ∨ ((True ∨ True) ∧ p4)) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57760196624273637885608268647 : ((((p3 → p3) → p3) → (p4 → (((((p5 ∨ (((p1 → p1) → p2) ∨ p1)) ∨ ((p4 ∧ p2) ∧ p3)) ∨ p4) ∨ (True ∨ p3)) ∧ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147342672433301458164029192804 : ((((((((False → True) ∨ p3) → (p4 ∨ p3)) ∧ ((p2 → p2) ∨ True)) → (p5 ∧ False)) → (p2 → p4)) ∨ p1) ∨ (p2 → ((p5 → True) ∨ p1))) := by
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
theorem thm_5_vars_756426018998251687435214683665 : (((p1 ∧ ((((p3 → ((p1 ∧ (((p4 ∧ True) ∧ False) → (p1 → False))) ∧ True)) ∨ (p5 ∨ (True ∨ p3))) ∨ p4) → (p3 ∧ (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134138890994089625057456113210 : ((((False ∨ ((p5 → ((((p3 ∧ p5) → True) ∨ p2) → (p4 → p3))) ∧ (p4 → (p1 → p1)))) → (p2 ∨ p2)) ∨ True) ∨ (True ∨ (p5 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147294615120818535324130737836 : ((((((((p1 ∨ ((p1 ∧ p2) ∧ True)) ∨ False) → False) → ((False → p2) → (False ∧ p2))) ∨ p5) → False) ∨ p5) ∨ ((p4 ∨ (True ∨ False)) ∨ p1)) := by
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
theorem thm_5_vars_762063759336079174587270762104 : (((p3 ∧ (((((False ∧ ((False → p5) → ((p5 ∧ p4) → p1))) → p3) → (p1 → (p2 ∧ ((p3 → p4) ∧ p1)))) ∨ p4) ∧ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198335952958535531393514520849 : ((p2 ∧ ((((p2 → p4) ∨ p2) ∧ p3) → p2)) ∨ (((p3 → p4) ∧ ((p2 → p4) ∧ ((p3 ∧ (True → False)) ∧ p2))) → (p1 ∨ (p1 ∧ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150064600264483332553636431195 : ((True → (((((p1 ∧ (True → True)) ∨ False) ∨ True) ∧ (p5 ∨ ((p2 ∨ p4) ∨ p4))) → ((p4 ∨ p1) ∨ True))) ∨ (True → ((p1 → p4) → p1))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590625815000531790308883838217 : (((((p2 ∧ ((False → p4) ∨ ((False → p3) ∧ (p5 ∨ ((False ∨ ((p3 ∧ (True ∨ ((p3 ∧ p3) ∧ p2))) ∨ p3)) ∧ False))))) → False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171452422636783898780634515695 : (((p3 ∧ ((p3 → ((p5 ∧ p1) ∨ ((p3 → False) ∨ True))) ∨ (True ∧ p1))) ∧ True) ∨ ((p5 ∨ (False → (p3 → p3))) → (p4 ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350106052628865664147190086512 : (p4 → ((((((p4 → p1) ∧ (p5 → ((False ∧ p2) ∨ (p1 → False)))) ∧ (False → p4)) → (p3 ∧ True)) ∧ (((p3 ∨ p5) ∨ p3) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308592521342828090963175931126 : (p2 ∨ (((p3 ∧ (True → p5)) ∨ (((p3 → (((((p4 ∨ p2) → (p1 ∨ p4)) → p5) ∨ False) ∨ p5)) → (p4 ∧ (p1 ∧ False))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621035116306329878172037043417 : (((((p1 → False) → ((((p5 ∧ p1) → (((p5 ∧ (p3 ∧ (p4 → True))) ∧ ((p1 ∧ True) ∨ (True ∨ p1))) ∨ p5)) ∧ True) → False)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62253947643659017690500820274 : ((p3 ∧ ((p3 ∨ ((((p3 ∧ (p4 → p5)) ∨ (((p5 ∨ (p1 ∧ ((p3 → p4) ∧ (p5 ∧ p5)))) → p1) ∧ p2)) ∧ p4) ∨ p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160043148746835056663889790661 : ((((True ∨ p4) → ((((p4 ∨ (p4 ∧ True)) ∧ True) → (True ∧ p4)) → ((p1 → True) ∧ p5))) → False) → ((True → (False ∧ (p2 → p2))) → p1)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115780433909097988959762078305 : (((((True ∧ p5) → False) ∧ p3) ∧ (((p4 → ((False ∧ True) → p2)) ∨ p4) → (((p2 → (p5 → (p4 ∧ False))) → p4) ∧ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353912623870487718351431316732 : (p4 → (p2 → (((((p4 ∨ p5) ∧ True) ∧ p5) ∧ ((p5 → p2) → ((p3 ∨ (p3 → (p3 ∧ p5))) → (p1 ∨ p1)))) ∨ (True → (p4 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638599331217187322233932880759 : (((((p5 ∨ (((p1 → p4) ∧ True) ∨ p5)) ∨ ((((False ∨ p1) ∧ p3) ∨ (p5 ∨ ((p1 ∧ p1) ∧ p3))) → (p2 → (p5 → p3)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307726135075089456131765780598 : (p1 ∨ (p3 → (((((((False ∧ p4) ∧ p1) ∧ (p5 → p2)) ∧ (p5 ∨ ((p2 ∧ p2) → ((True ∨ (p1 ∧ p2)) ∧ p4)))) ∨ p1) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672110588999122218836326036629 : ((((((False ∧ (p5 ∧ p4)) → ((((p2 → (False ∧ (p4 ∨ p4))) ∧ (False ∧ p5)) ∧ False) ∨ (p5 ∨ p5))) ∨ p4) → (p2 → (p1 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217418267576881673391834437326 : (((p1 → (False → p3)) ∨ p4) → (((True ∨ p3) → p4) ∨ (p4 → (((p1 → True) → (p5 ∧ (p4 ∧ (p3 ∧ p1)))) → (p5 ∨ (p4 ∧ p3)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319868199552152586560522407722 : (p4 ∨ (((p3 → (p1 → p4)) → p1) ∨ (p1 ∨ ((((p4 ∨ p4) → False) ∨ ((p2 ∨ p4) → ((True ∨ False) ∨ (p3 ∧ (p2 → p5))))) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47649641264358508311889256094 : ((((((True → True) → (((p5 → ((True → (p1 ∨ True)) ∧ (True → p3))) ∧ p3) ∨ (p2 ∧ False))) ∧ (p3 ∨ p3)) ∧ p5) → (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161337654846595936713914905653 : ((True ∧ (p4 → (p1 ∧ (True ∨ (((p1 ∨ p3) → True) ∨ ((False ∧ p2) ∨ (True ∧ (p5 ∧ p5)))))))) → ((p2 → (p4 ∧ (p4 ∧ True))) ∨ True)) := by
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
theorem thm_5_vars_262150197225244225177788187246 : (True ∧ ((((p3 → ((p1 ∨ ((p5 ∧ True) ∨ (p3 → ((False ∨ p4) → (False ∧ (False ∨ p1)))))) → (p1 ∧ p3))) → (p2 ∨ p3)) ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148692844112866333342057319123 : (((p1 ∨ (True ∧ ((p1 → (False ∨ p5)) ∧ False))) ∨ ((((p1 ∧ p1) ∨ p1) ∨ p1) ∧ ((True → True) ∧ p2))) ∨ ((p3 ∨ (True → True)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306270037584575932551186671007 : (p1 ∨ ((p4 → (False ∨ p5)) → ((((p5 ∨ (((p3 ∧ p1) ∨ ((p2 ∧ (p2 ∨ p4)) → False)) → p5)) ∧ ((p1 ∨ p4) ∧ p5)) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719193462125972306446258201364 : ((((p2 ∧ (False ∧ (p1 → p1))) ∨ ((p2 → p1) → ((((p3 → p5) ∨ (p4 ∧ p4)) → (((p1 → p1) → p2) → (p5 → p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42249852295067050038860705026 : (((p1 ∧ (((p2 ∨ ((p3 ∨ ((p1 ∨ False) ∧ (False → (p1 ∨ (p5 → (p1 ∨ False)))))) → ((p3 ∧ p1) ∨ False))) ∧ True) ∧ p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63304149624515022247269123578 : ((p5 ∧ ((p3 → (True ∧ True)) → ((p1 ∧ p4) → ((((p3 ∧ ((p4 ∧ (True ∧ p4)) ∨ p5)) ∧ True) ∧ p1) ∨ (p3 ∨ (p1 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135739997531580005307400194688 : ((((((True → True) → (False ∧ p2)) ∧ (p4 ∧ p5)) ∧ (p3 → (p5 ∧ True))) ∨ ((p2 ∨ ((p4 ∨ True) → p2)) → True)) ∨ (False ∨ (p4 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602533468681693474048343144260 : ((((False ∨ ((((p3 ∧ ((((True ∨ (True ∧ p1)) ∨ p2) ∧ p4) → (p2 ∨ (((p3 → False) ∨ p5) → True)))) ∧ p4) ∧ True) ∧ p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204145914157113002186532038714 : (((((p1 ∧ False) ∧ True) ∨ p5) ∧ p1) ∨ (p2 → ((p1 → (p2 ∧ ((((p4 ∧ False) → True) → (True → p3)) ∨ p1))) ∨ ((p3 → p5) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134242562635118553517755677685 : (((((p2 ∨ (p2 ∨ p5)) → p5) → (((((True → False) ∨ (p1 ∧ p4)) ∨ ((True ∧ p1) → p2)) ∨ p2) ∧ p3)) ∨ True) ∨ (p5 ∨ (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187114471648407819227782335008 : (((p3 ∧ p3) ∨ ((False ∨ p4) ∨ (p2 ∨ ((p3 ∨ True) → p5)))) → (p4 ∨ ((True → False) → (p3 ∧ (((p4 ∧ p4) ∨ False) ∧ (p2 → p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
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
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- False on the left can always be used.
        apply False.elim h19
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h21 := h17 h20
        -- False on the left can always be used.
        apply False.elim h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h24 := h17 h23
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- False on the left can always be used.
        apply False.elim h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h30 := h26 h29
        -- False on the left can always be used.
        apply False.elim h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h33 := h26 h32
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180541568604587235245261200641 : ((((False ∨ p1) → (False ∧ ((p4 ∨ p1) ∨ p2))) ∨ (True → (False ∧ p5))) → (p3 → ((p2 ∧ ((((p4 → p4) ∧ p2) ∨ False) → p1)) → p4))) := by
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
  cases h1
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (((p4 → p4) ∧ p2) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123193702314759039141316031853 : ((((((True → (False → p1)) ∧ ((p1 ∨ p3) → p3)) ∧ ((True ∧ (p1 → p3)) → False)) ∧ p2) ∧ (p1 ∧ ((p3 → p2) ∨ False))) → (p3 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : (p1 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h17.left
  let h25 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h27 : (True ∧ (p1 → p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h28
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h29 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h30 := h23 h29
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h31 := h21 h27
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53489830725525782299187608832 : (((p5 ∧ (((p3 → (p2 → (p4 ∨ p2))) ∨ True) ∨ (p4 ∨ p1))) → (((p1 ∨ p3) ∧ False) ∨ ((True → True) → (True ∧ (False ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160312222960357555446021403022 : ((((p3 ∨ ((p4 ∨ (p2 ∧ p1)) ∧ p2)) ∧ (p3 ∧ ((p3 ∧ p2) → (True → p5)))) → (p3 → p3)) → (((p4 ∨ (True ∨ p2)) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680865899019265569023214841005 : (((((p4 ∧ (False ∨ p5)) → (((False → (p4 ∧ ((((False ∨ p2) ∧ False) ∧ p2) → True))) ∨ False) ∧ p4)) → ((p3 → False) → (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690811944488910275538312234058 : ((((((p1 ∨ False) ∨ (True → ((p4 → ((True ∧ (p5 ∧ p3)) ∧ p3)) ∧ p3))) → p5) → (p3 ∨ ((p3 ∧ ((p4 ∨ p2) ∨ p2)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671058082061955155728031554795 : ((((False ∨ (((((((False → p2) ∧ p4) ∧ (p4 → p1)) ∧ p3) ∨ p3) ∧ (p1 ∨ ((p4 ∨ p4) ∨ p3))) → p2)) ∨ ((p5 ∨ p2) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_158270293772067222604083432498 : (((p1 ∨ (p5 → p3)) ∨ ((p5 ∨ (p2 ∧ (p4 → ((p4 → p4) → (p4 → p1))))) ∨ (True ∨ False))) ∨ ((p1 ∨ (p3 ∧ (p1 → p5))) ∧ p3)) := by
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
theorem thm_5_vars_347206339730290671400070098047 : (p3 → ((p5 ∧ (((p2 ∨ (p5 → (p2 ∧ p4))) ∨ False) ∧ (p1 ∧ p4))) ∨ (True → ((False ∧ ((p5 ∧ p1) → False)) → (True → (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41071809815454673350692409029 : ((((p5 ∨ (((p3 ∧ p5) ∨ ((p4 ∨ False) ∧ (p3 → (p3 ∨ ((False → p5) ∧ False))))) ∧ (p1 → (p5 ∧ p2)))) → (p2 ∧ True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255589962951247420270633123790 : ((p5 ∧ p3) → (p2 ∨ ((p2 ∨ ((p1 ∧ ((False ∧ p3) ∧ (((p4 → p4) ∨ p3) → (p3 → ((False → p4) → (p4 ∧ p2)))))) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308482796447070020268314203781 : (p2 ∨ ((((p4 → p3) → ((p4 ∧ (False ∧ (p1 ∨ (p1 ∨ (((False ∨ True) → p3) ∨ (p5 → p3)))))) ∨ True)) ∧ (p4 ∨ (p1 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105737572106548721095676358747 : ((((True ∨ (False ∨ p1)) → (((p3 ∧ p5) → p4) → (False ∧ (True → (p1 → p2))))) ∨ (True ∨ ((p3 → p3) ∧ (p2 → p2)))) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662059177797258001901970120137 : (((((((True ∧ p3) → False) ∨ (p1 ∧ ((p4 → True) → (p2 ∧ p4)))) ∧ (((((p3 ∧ p5) ∨ p1) → p3) → p2) → p4)) → (False ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55468625994973149039769512839 : ((((True ∧ (False → p3)) ∧ (True ∧ True)) → (True ∧ ((((p3 → p2) → ((p4 ∨ p5) → False)) ∧ (False ∨ ((p4 ∧ True) ∨ False))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336389093870531485622203429853 : (p1 → ((p1 ∧ (p2 → ((((True → (p3 ∨ ((False ∨ (p2 ∧ (p3 ∧ p5))) → (False ∧ p2)))) ∨ p5) ∨ ((False ∧ p5) ∧ False)) ∨ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254879717964257019160332698030 : ((p4 ∧ True) → ((False ∧ (p5 ∨ ((p2 ∨ ((p2 ∧ (p5 ∧ (p2 → True))) ∧ ((True → (p2 ∧ True)) ∧ ((p3 ∧ p5) → True)))) → False))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688739856135013063746942923423 : ((((p2 → (p2 → (((p4 ∧ ((p2 ∨ p5) ∧ p3)) ∨ (p5 ∨ (p2 ∨ p1))) ∧ p5))) ∧ (((True → ((False → p3) → p4)) ∨ p2) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184153722037605034192935248707 : (((p2 ∨ ((((p1 ∧ p2) ∧ (False ∧ p3)) → p1) → p3)) ∨ True) ∨ ((True → (p5 ∧ (p1 ∧ (((False ∨ False) ∧ (p1 → p1)) ∨ p5)))) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112272143835945128896017155417 : (((True → ((((p4 ∨ (p1 → ((p3 → p4) ∧ p1))) ∨ (True → ((((False ∧ p3) → p3) → p2) ∧ True))) → p4) ∧ p5)) ∨ True) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161524862124628246853752987417 : ((p4 ∧ (p5 → ((p1 ∧ ((((True ∧ p2) ∨ p3) ∧ p1) ∧ (p2 → (False ∨ True)))) → (p5 → p5)))) → (p3 ∨ ((p5 → (p1 ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171943638879086231519180779709 : ((((False → (p5 ∧ (((p5 ∨ p1) ∧ p5) → p4))) ∧ (False ∧ p3)) ∧ (p1 ∨ False)) ∨ ((p3 ∧ ((p3 → (False → p5)) ∧ p1)) → (p2 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199857566144313610291677204631 : (((p1 ∨ (True ∧ (p1 → p1))) ∧ (p5 → p4)) → ((((p1 ∧ False) ∧ p5) ∨ (((((p1 ∧ True) → p1) → True) ∧ True) ∨ p3)) ∨ (p3 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350030762809899054046325552605 : (p4 → ((((((p2 ∧ False) ∧ p4) ∨ (((p3 ∨ (p2 ∨ True)) ∨ p4) ∧ (True ∧ p2))) ∧ ((p1 ∧ p1) → (p3 ∧ (True ∧ p2)))) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148759381217028580491376131318 : (((False → ((p1 ∨ (True → True)) ∨ p2)) ∧ ((((False ∨ (p5 ∨ p5)) ∧ p5) ∨ ((False ∧ True) ∧ p4)) ∨ True)) ∨ ((True → (False ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63196212251059202696401685336 : ((p5 ∧ ((((p5 → (p3 → ((((p4 ∨ ((p2 ∨ p3) ∨ p3)) ∨ p1) ∧ False) ∨ p3))) ∧ False) ∨ (False → p2)) → ((p4 ∨ p2) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81046824677483010412249291172 : ((((((p1 ∨ (p3 → (p5 ∨ p3))) → p3) → p3) ∧ (((((p5 ∧ (True → True)) ∨ p1) → p2) ∨ True) → False)) ∧ ((False ∨ p3) ∨ p2)) → False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : ((((p5 ∧ (True → True)) ∨ p1) → p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : ((((p5 ∧ (True → True)) ∨ p1) → p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55597283822734493753942083799 : (((p5 ∨ ((p1 ∨ p3) → (p1 ∨ True))) → (False ∨ (((p3 ∨ False) ∨ ((((p5 ∧ (p5 → (True ∧ False))) ∧ p1) → p1) ∨ p5)) ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_217554928344276388625285660390 : ((((p2 ∧ p2) ∨ True) → p2) → (p4 ∨ ((p2 ∨ (p2 ∨ (((((p1 ∧ False) → p5) ∨ (p5 ∧ (p1 → True))) ∨ True) → p4))) ∨ (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620691663531379877849535421697 : (((((p1 ∧ p4) → ((p4 ∨ p4) → (((p1 ∨ p3) → ((True → ((p5 → (p5 ∧ (p3 ∨ p1))) → (p2 ∨ p2))) → p3)) ∨ p5))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84136692678139240075309093285 : (((p1 ∧ ((p1 ∨ ((True ∧ p5) → ((p3 ∧ p2) → ((False → False) ∨ p3)))) → False)) ∧ (True ∨ ((p4 ∧ p1) → (False ∧ (True ∨ p2))))) → p4) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ ((True ∧ p5) → ((p3 ∧ p2) → ((False → False) ∨ p3)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ ((True ∧ p5) → ((p3 ∧ p2) → ((False → False) ∨ p3)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185381279350409140150091618398 : ((p5 ∧ ((p3 → (False ∨ False)) ∧ (((p3 ∨ p1) ∨ True) → p3))) ∨ ((((p5 → p1) → ((False ∧ False) → p1)) ∧ (p5 ∨ True)) ∨ (p2 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308452502742135192214670052926 : (p2 ∨ ((((p5 ∨ p2) ∧ (p5 → (((((False ∨ (p3 ∨ True)) ∧ False) ∧ True) → (p4 ∨ ((p3 ∧ p5) ∨ p3))) ∧ p3))) ∧ (p5 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51143125805860837897645665805 : (((((((((p5 → p1) ∨ (p5 ∧ p4)) → False) ∨ (p3 ∨ False)) ∧ p5) ∨ (p4 → p4)) → p4) ∨ (p4 → ((False ∧ p1) ∨ (p1 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8310970858382124871456955122 : (((((((False ∧ ((p5 ∧ (False ∧ True)) ∨ p5)) → ((p1 ∧ (False → p2)) ∨ (True → p2))) ∨ p1) ∧ ((p5 ∧ False) ∨ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65711987092469483212863212298 : ((p4 ∨ ((((((p3 ∧ p5) → (False ∧ p4)) → p3) → (((False ∨ ((True ∧ p5) ∨ p3)) → p4) ∧ (p3 → p2))) ∨ True) ∨ (False ∨ False))) ∨ p4) := by
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
theorem thm_5_vars_685088579311559070049062228561 : ((((p1 ∨ ((((p3 ∧ ((p5 ∨ ((True → (p4 → p5)) ∨ False)) → p4)) → p2) → p4) → False)) ∨ (((p3 ∧ p1) ∨ (p4 → True)) ∨ False)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300667719094237901651095711424 : (False ∨ (((False ∧ (((p5 ∧ ((p2 → p5) → (True → p2))) ∧ ((p2 ∨ True) ∧ p4)) ∨ False)) ∨ True) ∨ ((((p4 ∧ p3) → p5) ∧ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65062758062030308618713221078 : ((p2 ∨ (p3 ∧ ((p2 ∨ ((((p4 ∧ p3) ∧ p1) → ((p3 → (p1 ∧ p5)) → False)) → ((p1 → p4) ∧ p3))) ∨ ((p1 → p5) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43560008067642033603103558461 : ((((((((p4 ∧ True) → (((p1 → p5) ∧ p5) → p3)) ∧ (p5 → p2)) ∧ ((p1 ∧ ((p5 ∨ True) ∧ p1)) ∧ p5)) ∧ p4) → True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43950700041598697144708802899 : (((((p3 ∧ True) ∧ ((p1 ∧ p4) ∨ ((p5 → False) ∨ ((((False ∧ p3) → p1) → (p2 ∧ p2)) ∨ (p5 → p3))))) ∨ (p5 ∧ p1)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62921795669713908323564682045 : ((p4 ∧ (False ∧ ((p1 ∧ p3) ∧ ((p1 ∧ p1) ∨ (((p5 ∨ (((p4 ∨ (p4 ∧ False)) → (p1 → p3)) ∧ p3)) ∨ p4) → (p1 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191310842983793727485648111862 : (((p4 → p5) ∧ (((p4 ∨ (p3 ∨ p4)) → p1) → p5)) ∨ (p2 ∨ (((False → (p2 ∨ ((False → (True ∧ p1)) ∨ False))) ∨ True) ∨ (p1 ∨ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150523900379122720204420964706 : ((((p4 ∨ ((p5 ∨ p5) ∨ ((p2 ∧ (p4 → p3)) ∧ False))) ∧ ((p1 → p3) → (False ∧ (p5 → p2)))) ∧ p3) → (p3 ∧ ((p5 → p3) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h35 =>
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h36 : (p1 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h37
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h38 := h34 h36
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h43 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h44
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h45 := h34 h43
        -- We need to get the left conjuct of h45 based on <expert-advice>.
        let h46 := h45.left
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h48 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h49
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h50 := h34 h48
        -- We need to get the left conjuct of h50 based on <expert-advice>.
        let h51 := h50.left
        -- False on the left can always be used.
        apply False.elim h51
    case inr h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h52.left
      let h54 := h52.right
      -- Conjunctions on the left can always be decomposed.
      let h55 := h53.left
      let h56 := h53.right
      -- False on the left can always be used.
      apply False.elim h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_883367273314607760101755567431 : (((((((False ∨ True) ∨ p4) → False) ∧ (((p5 ∧ p2) ∨ (((p2 ∧ p4) ∨ (p5 → ((True ∨ p1) ∨ p5))) ∧ p5)) → p3)) ∨ (p5 ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∨ True) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356472918697171367760450165107 : (p5 → (((True ∨ ((p5 → p2) ∨ p1)) ∧ ((p2 ∧ (p4 → p5)) ∨ p5)) → (((False ∧ p5) ∨ (True ∨ p1)) ∨ (False ∧ (p2 → (False ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43655955903006418144624057691 : (((((((False ∧ ((True → p4) ∨ (p2 ∧ False))) ∨ ((True → p5) → (p3 → (True ∧ True)))) ∧ p4) → (p2 ∨ (True → p1))) → p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123215103415772748403462428407 : ((((True ∨ (p2 → (((p5 ∧ (p1 ∨ (p4 ∧ True))) ∨ ((p1 → p1) ∨ False)) ∨ p4))) → p4) ∧ (p2 ∧ ((p1 → p4) ∨ False))) → (True → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (p2 → (((p5 ∧ (p1 ∨ (p4 ∧ True))) ∨ ((p1 → p1) ∨ False)) ∨ p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42805659188506898893532162056 : (((p1 → ((((p2 ∨ ((p4 → (p5 ∨ p3)) ∧ False)) ∨ (((p3 ∨ False) ∨ p5) → (True ∧ p4))) ∧ ((True ∨ p5) → p1)) ∨ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40799983864822208822562937394 : ((((True ∨ (p2 ∨ ((((p4 → (p4 ∧ True)) ∨ p1) ∧ (((p2 ∧ True) ∨ (p1 → p2)) ∧ ((p1 ∧ p5) ∨ p5))) → True))) → p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



