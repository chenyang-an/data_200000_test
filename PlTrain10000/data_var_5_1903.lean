variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149149737599744968946680908547 : (((False ∨ p3) ∧ (p2 ∧ (p2 ∨ (((p3 ∨ ((((True ∨ True) → p3) ∨ p4) ∨ p1)) ∧ p4) ∧ (p4 ∨ p5))))) ∨ ((True → True) ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624144926831245645761770310882 : ((((p2 ∨ (False ∨ ((p1 → p2) ∨ ((((p4 ∧ (p4 ∧ ((True ∨ (p5 → (p3 → True))) ∧ p1))) ∧ p4) ∨ (p2 ∨ False)) ∧ True)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47500982131628887394074744034 : (((p1 ∨ (((True ∨ p4) ∧ p2) → (((True ∨ p2) → (p1 ∧ (((p3 ∧ p5) → False) ∧ (False ∧ (p5 → p1))))) → p5))) ∨ (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691995805423619416496277215631 : ((((((((p2 ∨ (True ∨ p5)) → False) ∨ ((p4 ∨ True) → True)) ∧ p4) ∧ p3) ∧ ((p1 ∧ p3) ∨ (((p4 → (p1 ∧ p2)) ∨ True) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225191124808515109645383703145 : (((p4 ∧ p3) ∧ False) ∨ ((p3 ∧ (p2 ∧ (True ∧ (p4 ∧ ((p1 ∧ (True ∧ p3)) ∧ (p1 ∨ p5)))))) ∨ (((p4 ∧ p1) ∧ (p1 ∨ p1)) → p4))) := by
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
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204561023460349416556159019393 : ((((False ∧ p2) ∧ (p1 → p2)) ∨ p2) ∨ ((True ∨ p3) → (p5 ∨ ((((p3 ∨ True) → False) ∧ (p2 ∨ ((p2 ∧ True) ∨ p1))) → (p5 → p4))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h17 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h18 := h5 h17
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h25 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h26 := h22 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h31 : (p3 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h32 := h22 h31
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h34 : (p3 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h35 := h22 h34
        -- False on the left can always be used.
        apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204391943880032602314365634932 : (((False → ((True → p2) ∧ False)) ∧ p3) ∨ ((((((p2 → p4) ∨ True) ∧ False) → True) ∧ p1) → (((p5 → p2) ∨ (True ∧ p4)) ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_177882472952627164547759702028 : ((((((p2 → True) ∧ p4) ∨ ((p4 ∨ p1) ∨ (p5 ∨ p2))) → False) ∨ p5) ∨ ((p4 → ((False ∨ p1) → p3)) ∨ ((p1 ∧ (False ∧ p5)) → False))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693940830542832621159795900642 : (((((True → (((p3 ∨ (True ∨ p5)) ∨ p5) ∨ (False ∧ p2))) ∧ (p1 ∨ p2)) ∨ ((((p5 ∧ (p2 ∧ p2)) ∧ p3) ∨ (p2 → True)) ∨ p2)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_354922734306113253165942788953 : (p5 → ((p2 ∨ ((((((False ∧ p2) ∨ p5) ∧ p4) → False) ∧ (((p4 ∧ (p4 ∧ ((p1 ∧ p5) ∨ p5))) ∨ p5) ∨ True)) ∨ (True → True))) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186182649191530479964866579093 : (((p3 ∧ (((p1 ∧ (p3 ∧ p2)) ∧ p1) ∧ (p5 ∨ p4))) ∨ p5) → (((p5 ∨ (False ∨ ((False ∨ (p1 → False)) ∧ p5))) ∨ (p4 ∧ p3)) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138154192593771028386903438567 : ((p1 → (((p5 ∨ (False ∧ ((p3 ∨ ((False → p1) ∧ p3)) ∧ (p3 → p3)))) → (p2 → (False ∨ (False → p4)))) → p3)) ∨ ((False → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37792672744747773395390433488 : (((((p5 ∨ False) → (((((p2 ∨ True) → p3) ∧ p4) ∧ ((p4 ∨ (p5 ∨ True)) → True)) ∧ (p3 ∧ (p3 ∨ (p2 ∨ p1))))) → p2) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806479744761917135731597488272 : (((p4 → ((((True ∨ (p1 ∧ (False → p3))) ∧ (((True → (p1 ∧ (p1 ∨ (p2 ∧ False)))) ∨ True) ∨ (True → (False → True)))) → p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172654088334298250657701170225 : (((p4 ∨ p5) ∧ (((p5 ∨ (p1 ∨ (True → (False ∧ (p4 ∧ p3))))) → p4) ∨ p2)) ∨ ((False → (p3 ∨ (False ∧ p2))) ∨ (p1 ∧ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80937067087139358255194202583 : ((((True ∨ (((p1 ∨ ((p3 ∧ p1) ∧ (((False ∧ False) ∨ True) → p4))) ∧ p4) → (p2 ∨ (p3 ∨ p2)))) → p2) ∧ (True ∧ (p2 → p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ (((p1 ∨ ((p3 ∧ p1) ∧ (((False ∧ False) ∨ True) → p4))) ∧ p4) → (p2 ∨ (p3 ∨ p2)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260024144039112069201721787554 : ((p2 → True) → (p3 ∨ (((p1 ∨ ((((p5 ∨ False) ∨ p2) → p1) ∨ (((p2 ∨ p1) ∧ ((p2 ∨ False) ∧ p1)) → True))) ∨ False) ∨ (p3 ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242992382657061374326704587447 : ((p4 → True) ∧ ((p1 → (p3 ∧ (((p2 → p3) → p4) ∨ (((p5 ∨ p4) → p2) → (p5 → (False ∨ p3)))))) ∨ ((False ∨ True) ∨ (p4 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54915312355990152855093766412 : (((((p5 ∨ (False ∨ p3)) ∨ p4) → False) ∧ ((p3 ∨ (((False ∧ p4) ∨ (p3 ∧ p3)) → (p2 → ((p2 → True) → False)))) ∧ (p2 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178559395445429585116204630232 : ((((p2 ∨ (p1 → (True → p4))) → p2) ∧ (((p4 ∨ p4) ∨ False) ∨ False)) ∨ ((p1 → (False ∨ (p5 ∨ p4))) → (p2 ∨ (False → (p5 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260780374830576209003993576412 : ((p3 → p5) → ((p4 ∧ ((p5 → (p5 → (False ∧ p3))) ∨ ((True ∨ ((p4 → p1) → (p2 → ((p2 ∨ True) ∨ False)))) → p3))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320130957502097467216468770290 : (p4 ∨ ((True → (p3 ∧ False)) → ((((p2 ∧ (((p5 ∨ True) ∧ p1) ∧ p2)) ∨ p1) ∧ p1) → (p2 → ((False ∨ (True ∧ p4)) ∧ (False → False)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626058793294660315211531642152 : ((((p2 → (p3 ∧ ((False ∧ p3) ∧ (p5 ∨ (p4 → (p4 ∧ (p4 ∧ (((((p1 ∧ p3) ∨ (True ∧ p5)) → p5) ∨ True) → p5)))))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_147754536851970086785795061043 : ((((True ∨ (p1 → p5)) ∨ (p3 ∨ ((((p4 ∨ p2) ∧ (p2 ∧ p1)) ∧ ((p4 ∨ p2) → False)) → p2))) → False) ∨ (((p2 ∧ p4) ∧ False) → p1)) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134369832249824204751023505609 : (((p2 ∨ ((((((p2 ∧ (p1 → p4)) → p2) ∧ p4) ∨ (p3 → p3)) ∧ p2) ∧ ((p2 ∧ (False ∧ p1)) ∨ p5))) ∨ p2) ∨ (p1 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193793998264858727549262486486 : ((p4 ∧ (p1 ∧ (p1 → (((True → p3) ∨ False) ∧ p5)))) → (((p3 ∨ (True → (p5 → p3))) → False) → ((p2 ∧ p3) ∨ (p2 ∧ (False ∧ False))))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ (True → (p5 → p3))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h11
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192991351066996789305678058773 : ((((((p2 ∨ p4) ∧ p1) ∨ p4) ∨ True) → (False ∧ False)) → ((((p3 ∨ (p3 ∨ ((p3 ∨ p5) ∨ (True ∧ p3)))) → (p1 ∨ True)) ∧ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ p4) ∧ p1) ∨ p4) ∨ True) := by
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
theorem thm_5_vars_142667539163387146602817282691 : ((p1 ∨ ((((p4 ∨ p1) ∨ ((p3 ∨ False) ∨ (p4 → False))) ∧ True) ∨ (p5 ∧ (((p1 ∨ (p2 → False)) ∨ p4) ∨ p5)))) → ((p5 ∨ True) ∧ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
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
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338237875969831169913120126202 : (p1 → ((((False ∨ p1) ∨ p3) → (True ∧ p3)) ∨ (((p1 ∧ ((p3 ∧ p2) ∨ True)) ∧ p2) ∨ (False ∨ (((True → (p4 → p4)) ∧ True) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711023600188317434866033457054 : (((((p4 ∨ p2) → ((p2 ∧ p1) ∨ True)) ∧ ((p4 ∨ (((((p1 ∨ p1) ∧ (p3 ∧ p5)) ∨ p4) ∨ p5) ∨ (p3 ∨ False))) ∨ (p3 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809329875785760717550165367532 : (((p5 → ((p3 ∧ (p1 ∧ ((p4 ∧ p5) → (p3 ∧ (False ∧ (((p3 → (p3 ∧ (False → p1))) → ((p2 ∧ p3) → p5)) → p2)))))) ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_328821517749730978711870681165 : (True → ((((((True → True) ∨ p2) ∨ p1) ∨ p4) → (p5 ∧ p4)) → (((p1 ∨ (p2 ∨ p3)) → ((p3 ∧ True) ∨ (True ∧ p3))) ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664907130694921360840808769989 : ((((p3 → (((p1 → (False ∨ (p5 ∨ False))) → (p5 → ((p3 → (p3 ∨ (((p2 ∧ p4) → False) ∨ p3))) ∨ p1))) ∧ False)) → (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39002809636417148663591339344 : ((((p2 ∨ p3) ∧ ((p4 ∨ p1) ∧ ((((p5 ∧ True) ∧ p5) → (p3 ∨ ((p1 ∨ ((True ∨ p3) ∨ p2)) ∨ (p1 ∨ p3)))) ∧ p4))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119395484122270247539711798602 : ((p4 → ((p3 ∧ (((p5 → (p3 ∨ False)) → (p1 ∨ (((p2 → (p3 ∧ p5)) ∨ p4) ∨ (False ∧ False)))) ∧ (p3 ∧ p4))) ∧ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52035717147657406617749518642 : (((p4 ∨ ((p5 → False) → (p2 ∨ ((((p3 → p5) ∨ True) ∧ p2) ∨ (p4 ∧ True))))) ∨ (p1 ∨ ((True ∨ p3) ∨ ((p3 ∧ False) → p3)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_263390259289976831779209506742 : (True ∧ ((((((p5 ∨ p5) ∧ ((p4 → p3) → (p4 → (p2 ∧ p4)))) → p5) ∧ (p1 ∨ (True → False))) → (p4 ∧ p3)) ∨ ((True ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316715168449400077868226169292 : (p3 ∨ (p5 ∨ (p3 ∨ (((p3 ∨ ((False ∨ p4) ∧ ((p1 ∨ False) ∨ p5))) ∨ (False → (((p2 ∨ p2) → p1) ∧ (p3 ∨ (p5 ∧ False))))) ∨ p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458217518658541491816742635601 : (((((p3 → p5) ∧ ((p4 → False) ∨ ((((p4 ∨ ((p4 ∧ p4) ∨ p1)) ∧ p4) → p3) ∧ p1))) ∨ (True → ((p5 ∧ p2) → (p5 ∧ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219781678918038864450933346424 : ((p2 → (False ∧ (p5 ∧ p2))) → (((p4 → p3) → ((p3 ∨ (p2 → (p3 ∨ (p4 ∧ False)))) ∨ False)) ∨ (p1 ∨ ((p3 → (p5 ∧ p1)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696586921455017093408039462085 : (((((((p2 ∧ p4) ∨ (p4 → (p2 → (p5 ∨ p5)))) → p4) ∨ True) ∧ (((True ∨ p3) ∨ p1) → ((p1 ∨ False) ∨ ((p2 → p5) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611296134526283937270143941127 : ((((((False → True) ∨ ((p5 ∨ ((p2 ∧ p5) ∨ (p5 ∨ False))) ∧ ((((p2 → False) ∧ p2) ∧ p4) ∨ (True ∧ (p2 → p2))))) → p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_681370249293366042124371681822 : ((((p1 ∨ ((p5 ∨ True) ∨ ((p4 ∧ ((p3 ∧ (p4 ∧ True)) ∨ p5)) → ((False → (False ∧ p1)) ∨ p1)))) → (p5 ∧ (p3 ∧ (p2 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666764179533974005748241514180 : (((((((True ∨ (p1 ∧ False)) ∧ False) ∧ (p2 ∨ p5)) ∧ (False ∨ ((p3 ∨ (p5 ∧ (p4 ∨ False))) ∨ (p3 ∧ p2)))) ∧ ((False ∨ p4) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37349203878650507173544766097 : ((((((p1 ∨ ((p1 ∨ (True → ((((((p1 ∧ True) → p2) ∨ p5) → False) ∨ p5) ∧ (p4 ∨ p4)))) ∨ True)) ∧ p2) ∨ p2) ∨ p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731750882161135316001219793487 : ((((p3 → (p3 ∧ p4)) → ((False ∨ ((p4 ∨ (p1 → ((p5 ∧ p1) ∨ (((p2 → (p5 → True)) ∧ p1) → p3)))) → p3)) ∨ (p3 → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_171997591435227613020051890553 : ((((p5 ∨ (p5 ∧ ((p4 ∧ (p1 → (p5 ∧ True))) → p5))) ∨ True) ∨ (p5 ∧ p3)) ∨ (p2 ∨ ((p4 ∨ ((p2 → (False ∧ p5)) → p5)) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654581759880864971779048488063 : (((((p4 ∨ ((p4 ∨ p2) → ((p1 ∨ ((p3 ∨ p4) ∧ (p4 ∨ p5))) ∨ (False ∧ (((p4 ∧ p5) ∧ False) → p4))))) ∨ False) ∨ (p2 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_625607086930915531489013041600 : ((((p1 → (((p3 → (p2 ∨ (((p2 ∨ p4) ∧ p2) → p5))) → (True → ((p1 → (p1 ∨ (p2 ∨ True))) ∧ (p3 ∨ p5)))) ∨ True)) ∨ p1) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134474718786995389043875769429 : ((((p5 ∨ ((True ∨ ((p4 → True) ∧ ((p4 ∧ (True ∧ p2)) ∧ ((p2 ∨ True) ∧ (p3 → p1))))) ∨ p5)) ∧ p2) → p5) ∨ ((True ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76585680089255430643782087286 : (((((((((True ∧ (p4 ∨ (p1 → p4))) ∨ p5) ∨ (False → True)) ∨ True) ∧ (p4 → p1)) → False) ∨ (p2 ∨ (p2 ∨ (p4 → True)))) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((True ∧ (p4 ∨ (p1 → p4))) ∨ p5) ∨ (False → True)) ∨ True) ∧ (p4 → p1)) → False) ∨ (p2 ∨ (p2 ∨ (p4 → True)))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137777061732282185238541687244 : ((p2 ∨ (((((p3 ∧ False) ∧ p5) ∨ True) ∨ p5) ∧ (((p3 → False) ∧ (p5 ∧ p1)) ∨ (p1 ∧ ((p5 ∧ False) → p4))))) ∨ (True ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158546421824220994227138642233 : (((p3 → p5) → (p5 ∧ (((p3 ∧ p5) → (p5 → ((p2 ∨ (p4 ∨ (p2 → p4))) ∧ False))) ∧ True))) ∨ (False → (True → (p3 ∧ (p1 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196320232217402718415471551828 : ((p4 ∨ ((False ∧ (False ∧ (False ∨ p5))) → False)) ∧ (((((p1 ∧ p1) ∨ (p4 → False)) ∨ (p1 ∨ (False ∧ True))) ∨ False) ∨ ((False ∧ p4) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47810773943779195444374392218 : (((((True ∧ (((True ∨ p3) ∨ p4) → ((p2 ∧ ((p5 ∧ False) ∨ False)) ∨ (p4 → False)))) ∨ ((p1 → p1) → p2)) → p4) → (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64390782980293383209821962695 : ((p1 ∨ ((((p3 → p3) ∧ ((((p5 → False) ∧ ((p1 ∧ True) ∨ p3)) → (p2 ∨ p4)) ∨ ((p2 ∨ (True ∧ True)) ∨ p1))) ∨ p2) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209454122103936507046116186737 : ((p2 → (p4 → ((p4 → p4) ∧ p4))) → (p1 → (((p2 ∨ ((p5 → p4) ∧ ((p5 ∨ p3) ∧ p1))) ∨ (p3 ∨ p2)) ∨ (False → (True → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343449351680778386803517410814 : (p2 → ((p5 ∨ False) ∨ (((p2 → (False ∨ p5)) ∨ False) ∨ (True ∨ (((p4 → p4) → True) ∧ (((True ∧ True) → ((p4 ∨ True) ∧ p3)) ∨ True)))))) := by
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
theorem thm_5_vars_111929811365259440451845724968 : (((((p2 ∧ p3) ∧ ((False ∧ p3) ∨ ((False → False) ∨ p2))) ∧ (((p3 ∧ p3) ∧ ((False ∨ False) ∧ p5)) ∧ (p3 ∨ p3))) ∨ p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204825533390351166650339379388 : ((((p3 ∧ (p5 ∧ p2)) ∨ p1) → p2) ∨ (((False ∧ (False ∨ p3)) ∨ (((True ∧ True) ∨ p2) ∧ False)) ∨ ((True ∧ True) ∨ ((p3 → False) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134110937767642228866931964272 : ((((((p4 → p5) → p5) ∧ ((p2 → (((False ∧ p5) ∨ p5) ∧ (p5 ∨ (p2 ∧ False)))) → False)) ∧ (p5 ∧ p3)) ∨ True) ∨ ((p1 ∧ p2) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49212568238592356820221264323 : ((((p2 ∧ p1) ∧ (((p4 ∧ ((True ∨ p4) → p2)) ∨ False) ∧ (((p5 ∨ ((p4 ∧ p2) ∨ p2)) → p4) ∧ p4))) ∨ (False → (p4 → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65703917504867447471043701106 : ((p4 ∨ (((((p4 ∧ (p2 → ((p3 ∧ (p4 ∧ True)) → p1))) ∨ (p3 → p5)) → p5) ∧ (((p2 ∧ p5) ∧ p2) ∧ False)) ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748108248157243868093154974368 : ((((p1 → p3) → (((True → ((p1 → (((p3 → (p2 → True)) → (True ∧ p2)) → (True → p5))) ∧ p2)) ∧ ((True ∧ True) → True)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_797441384010316635586051869625 : (((p1 → ((False ∨ ((p5 ∨ p2) → ((p2 ∨ ((p3 → p5) ∨ ((((p1 → p1) → (True ∧ p5)) → p1) ∧ (p2 → p3)))) → p4))) ∨ p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_134740537673390646861697704395 : ((((p1 → p5) ∧ (p2 → (False → (((p1 ∨ (p2 → True)) ∨ (False → p3)) ∨ (((p3 → p5) ∧ True) → p4))))) → p3) ∨ (p1 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148103348977185534888206743278 : ((((p5 ∧ (p3 ∨ (p4 → (False → (True → (p2 ∧ (p1 ∨ (p2 → p3)))))))) → (p3 ∧ p3)) → (p4 ∧ p3)) ∨ ((True ∨ (p5 → p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51387095673612008308433203482 : (((((p4 ∧ True) ∧ (p3 → (((True ∨ ((p4 → p5) ∨ p3)) ∧ p5) → (p4 ∧ False)))) ∨ p1) → ((p3 ∧ p4) ∨ ((True ∨ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304019853156941153381927114449 : (p1 ∨ ((False ∧ (((p3 → p3) → (p2 → (p4 → p5))) ∧ (((False ∧ (p2 ∨ (p3 → (p2 ∨ p2)))) ∨ p1) ∧ ((True → p1) ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149453153406177909544561210700 : ((False ∧ (((p1 ∨ ((False ∨ p3) ∧ ((((p5 → True) ∧ (p3 ∧ p5)) ∨ p3) → True))) → False) ∨ (p1 → p3))) ∨ ((p4 ∨ True) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178328549137800592750295883317 : ((((p3 → ((True ∨ (False ∨ p3)) ∨ p2)) → (p2 ∨ p2)) ∨ (p5 → p3)) ∨ (False ∨ ((False ∨ ((p5 ∧ p1) ∨ ((p3 ∧ True) → p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307380983336285995140955913941 : (p1 ∨ (p4 ∨ ((p3 ∨ (((p4 → (p4 ∧ ((p4 ∧ p1) → (False ∧ (p5 → p3))))) → p5) → (p4 ∨ p4))) ∨ ((p4 ∨ (True ∨ p4)) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353514953333113962222247296432 : (p4 → (p2 ∨ (False ∨ ((((p3 ∧ p4) → p3) ∧ ((p5 ∨ (p1 → (p4 ∨ p4))) → ((((p3 ∨ p1) ∨ (p3 ∨ p1)) ∨ p3) → p3))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233505843858251487049864112412 : ((p1 ∨ (p4 ∧ p5)) → (((((((p4 ∧ (((p4 ∨ (p3 ∧ p1)) ∨ p3) → p4)) → True) ∧ (p1 ∧ p4)) → p5) → False) ∧ (True ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_608542571793896050843890878240 : ((((((p2 ∧ (p5 ∨ (p1 ∨ ((((True ∨ True) ∨ ((p2 → ((p4 ∨ p2) ∧ p5)) ∨ p2)) → p4) ∨ (p5 → p4))))) → p1) ∨ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186204348130014311247682597842 : (((p3 ∨ (((p4 ∨ (p3 → p2)) ∧ (True ∨ True)) ∨ p5)) ∨ True) → ((((p1 → (True ∨ ((True → p2) ∨ False))) → (p3 ∧ p2)) ∧ False) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
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
          -- Disjunctions on the left can always be decomposed.
          cases h7
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258853981372380062682921763302 : ((True → p1) → (((p3 ∧ p3) ∨ True) ∧ ((((p3 → p3) ∧ p2) ∧ ((False ∧ p3) ∨ p3)) ∨ ((p5 ∧ ((p5 ∧ p5) → (p5 → p5))) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161658153175205315947730766735 : ((p1 ∨ ((p5 ∧ ((p1 → True) ∨ p5)) ∨ (p5 → (p4 ∧ (((p4 → (p3 ∧ p4)) → p5) ∧ p5))))) → (p2 ∨ (p4 ∨ ((p2 → True) ∨ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4512674411211345455740917663 : (p3 → ((False ∨ (((((((p4 ∨ p3) ∨ p1) → (((False ∨ True) ∧ ((p4 ∨ p2) ∨ p2)) ∧ False)) → p2) → p5) ∨ p3) ∧ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50280952386525956756965394654 : (((((p3 ∨ (True ∧ ((((p3 → True) → (p2 ∧ p1)) → (p4 → p3)) → False))) ∧ p5) → (p1 ∧ False)) ∨ ((p2 → (p3 → True)) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754646507748657665441068435527 : (((False ∧ (p4 ∧ (((p2 ∨ ((p2 ∨ (((p2 ∧ ((p1 → True) → (p5 ∨ p4))) → p5) → p2)) ∧ False)) ∧ (p4 ∧ (p3 ∨ p2))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160620134575888123505818473346 : (((((p2 ∧ ((False ∨ (False ∧ p5)) → p5)) ∨ p5) → p5) ∨ (((p4 ∨ True) ∧ True) ∨ (p3 ∧ p4))) → ((p5 ∨ p2) ∨ ((True → False) → True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113090325787260045850026833804 : (((p5 ∨ ((p1 ∧ ((((p5 ∨ False) ∨ True) → p5) ∨ ((((True ∨ p2) → (p5 ∧ p1)) ∧ (p4 ∧ True)) ∧ p4))) → p2)) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206629573496639775503466047029 : ((p1 → (((p3 → p5) ∨ p4) → p4)) ∨ (True → ((False ∨ p5) → (((False ∨ p1) ∧ (p2 → p1)) ∨ ((p4 ∨ p2) ∨ ((p4 → p1) → True)))))) := by
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
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157027654607720699392572071248 : ((((p1 ∨ p5) ∨ ((p5 ∧ ((((False ∨ False) → (False ∨ (p2 ∨ p2))) ∨ p4) → p1)) → p2)) ∨ True) ∨ (True ∨ (False ∨ (p3 → (p5 ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785406212677051986863063081280 : (((p4 ∨ (((p5 ∨ ((p4 ∧ (False ∨ True)) ∨ (p4 ∧ (p5 ∧ (p3 → ((p4 → (p5 ∧ (p1 ∧ p4))) ∧ True)))))) → (p4 ∧ False)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_59180184907327756085077564056 : (((False ∨ p5) ∨ (p1 ∨ (((((p5 → p4) ∧ (False → (False → p2))) ∧ p5) → p4) ∨ (p4 → (True ∨ (True ∨ (p4 ∨ (p1 ∨ False)))))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305609808979587150137638708498 : (p1 ∨ (((((p4 ∧ True) → p3) ∨ ((p5 ∨ (p5 ∧ p5)) ∨ p2)) ∨ True) → (True ∧ ((p5 ∨ (p4 ∨ (((p2 → True) ∧ p3) → True))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
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
theorem thm_5_vars_353460914744666930921007929032 : (p4 → (p1 ∨ (p1 → ((p5 ∧ (((((p1 ∧ p3) → False) → (False ∧ p3)) ∨ False) ∧ p2)) ∨ ((p5 → (p2 ∨ p4)) → ((p1 ∨ p2) ∨ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756835575226382387196270821305 : (((p1 ∧ (((p2 ∧ ((p2 → p1) ∧ p5)) → (p2 ∨ p4)) ∧ (((p3 ∨ (((False → (p1 ∨ False)) ∨ False) ∧ p1)) → (False ∨ p1)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165928882327837135782480296714 : (((p3 ∧ p5) ∧ ((p5 ∨ ((p3 ∧ False) → p4)) → ((p2 ∨ (p4 ∧ (False ∧ p5))) ∧ p3))) ∨ ((p1 → p1) → (p3 → (p5 → (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260735159437096448139686996589 : ((p3 → p4) → ((((True → p3) ∧ p1) ∧ p2) ∨ ((p1 → p1) ∨ ((p2 ∧ p5) ∧ (p5 → (((p3 ∨ (p5 ∨ False)) ∧ (False ∧ p3)) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8204912937328794023432775771 : ((((p4 → ((((((p3 ∨ p1) → (p1 ∧ (p2 ∧ p1))) ∨ p4) ∧ p3) ∧ (((p4 → p5) ∧ (p4 → p3)) → p4)) → p1)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_204105360453992632692844723586 : (((((p2 ∨ p5) ∧ p5) ∧ True) ∧ p3) ∨ ((False ∨ (p5 ∨ (p1 ∧ ((p5 → (p5 → ((p5 ∧ p2) ∧ (p2 ∨ p4)))) ∧ p2)))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113837535517251315579581978908 : (((p2 ∨ ((p1 → (True ∨ (p5 ∧ p3))) → ((p1 ∧ (True ∧ p5)) ∨ (((p3 ∨ p3) → (p3 ∨ p5)) → p3)))) → (p2 ∧ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172964588354244159850161329526 : ((p4 ∧ (((p1 ∧ ((((p2 ∨ p5) ∨ p2) → p2) ∨ p1)) ∨ p5) ∨ (p3 → p2))) ∨ (p2 → (p1 → (p2 ∨ (False ∨ (p4 ∧ (p3 → p1))))))) := by
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
theorem thm_5_vars_320325312961331595453896055736 : (p4 ∨ ((p3 ∨ p3) ∨ ((False ∧ (p3 ∧ p2)) ∨ (p4 → ((False ∧ (p2 ∨ False)) ∨ ((False ∨ ((p3 → p5) → p4)) → (p4 ∨ (p3 ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124330101544136711476751326940 : (((p1 ∨ ((True → (True → (p2 ∧ p3))) ∨ False)) ∧ (p1 → (p5 ∧ (p4 → (p5 ∧ (False ∨ (p5 ∧ (p5 ∨ (p1 ∧ p5))))))))) → (p2 ∨ p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625615054022019606663048319347 : ((((p1 → ((False ∨ (False ∨ ((((((p3 ∨ (p5 ∧ (p2 ∨ p2))) ∨ (p4 ∨ p5)) → (False → p2)) ∨ p5) → p3) ∨ p5))) ∨ False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_757840526373389591393437944411 : (((p1 ∧ (p2 ∨ (((p1 → False) → (p2 ∧ p5)) ∨ (p2 → (((((p1 ∧ p4) → (p3 ∨ p4)) → p1) ∧ p1) → ((p2 ∧ p2) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



