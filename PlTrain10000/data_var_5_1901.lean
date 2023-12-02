variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2777315980592634832916068493 : ((((p4 ∨ p4) ∨ p3) → False) ∨ (((True → (False ∧ p2)) ∧ p4) → ((False ∨ ((p1 → ((p2 ∨ (False ∨ p1)) ∧ p1)) ∧ p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58805269523092876429665391442 : (((p5 → p2) ∧ ((p1 ∨ (p1 ∧ ((p5 ∨ (p2 ∧ (p1 → p2))) → (False ∨ (p3 ∧ (p5 ∧ (((p2 → True) → p5) ∨ False))))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137802200062594137010756943240 : ((p2 ∨ (True → ((p5 ∧ (((False ∨ ((p2 ∨ p5) → p2)) ∨ (p3 ∨ False)) ∧ (False → (p1 ∧ (p1 ∧ p2))))) ∨ True))) ∨ ((True ∧ p2) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64522838898694779494493233166 : ((p1 ∨ (((p4 ∧ ((p5 ∨ True) ∧ p3)) ∧ ((p4 → p2) ∨ p4)) ∨ (p1 ∨ (p1 → (True ∨ (((p2 ∧ True) ∧ (p4 ∨ p4)) ∨ p5)))))) ∨ p2) := by
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
theorem thm_5_vars_247426381495793667148175671960 : ((False ∨ p2) ∨ ((((False ∧ (((((p5 ∧ p1) ∨ p1) → True) ∧ (p2 ∧ p4)) ∨ True)) ∨ True) ∨ True) ∧ (p2 → (p5 → (p5 ∧ (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788361707864308344940779981585 : (((p5 ∨ (((((p5 ∧ (((p2 ∨ p5) ∨ (True ∧ (p5 ∨ False))) → ((p1 ∧ (p4 → True)) ∧ p5))) ∨ p5) ∨ False) ∧ (p3 ∧ p1)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_38022834326606940232812655118 : ((((p2 → (((p2 → p2) → (((p5 ∧ True) ∨ (p2 ∧ p4)) ∨ (((p3 ∧ p3) ∨ p1) ∧ (True ∨ False)))) ∨ p2)) ∨ (p2 ∨ p5)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55122964238465486398746117936 : (((((p5 ∨ p2) ∨ (p2 ∧ p3)) ∧ p1) ∨ ((((p2 ∧ p5) → ((p4 ∧ p1) ∨ (((p4 ∧ p1) ∨ p3) ∨ p4))) ∧ False) → (p3 → False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302009916787472408982096771351 : (False ∨ (True ∧ ((((p3 ∧ (((p4 → (True ∧ (p3 ∨ p4))) → p1) → ((p4 ∧ True) ∧ (((False → p3) ∨ True) ∨ p5)))) ∧ p1) ∨ p1) ∨ True))) := by
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
theorem thm_5_vars_355845440562955907366721379419 : (p5 → (((p1 ∧ (p3 → ((False → (((p1 ∨ p1) ∨ ((p5 ∨ (p4 ∨ p5)) ∧ True)) → (p5 ∨ p4))) ∧ True))) → False) ∨ (p4 ∨ (True → True)))) := by
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
theorem thm_5_vars_147734565165504736459871853732 : (((((False ∨ (p3 ∨ True)) ∨ p3) ∧ ((True → (True ∨ (p3 ∧ False))) → ((p1 → (p3 ∨ False)) ∧ False))) → False) ∨ ((p3 ∨ p5) ∧ (p5 → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : (True → (True ∨ (p3 ∧ False))) := by
          -- Implications on the right can always be decomposed.
          intro h9
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h10 := h3 h8
        -- We need to get the right conjuct of h10 based on <expert-advice>.
        let h11 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (True → (True ∨ (p3 ∧ False))) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (True → (True ∨ (p3 ∧ False))) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h18
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159040639546346634354763778473 : ((p5 ∨ (((p1 ∨ ((((False → (p5 ∧ (True ∧ p3))) → (p1 ∨ p5)) → p1) ∨ p4)) → False) ∧ p1)) ∨ ((p4 ∧ p4) ∨ ((False ∨ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133535572325727025597029722670 : ((((((p4 ∨ p2) ∨ p4) ∧ ((p4 ∧ (p1 ∨ p2)) ∨ (p4 ∨ (p3 ∧ (p2 ∨ (p3 ∨ (p5 ∧ p4))))))) ∧ p3) ∧ p3) ∨ (True → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51699979565183142425099317464 : (((((p1 → (p4 → ((True → False) ∧ (p4 ∧ p1)))) → p4) ∨ ((p4 → True) ∧ p3)) ∧ (p1 → ((p2 ∨ (p5 ∧ False)) ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686557086500990705755332101146 : (((((p2 ∨ p1) ∧ (True ∧ ((p2 ∧ (p4 ∨ (p3 ∧ (p3 → (p4 ∨ (p1 ∧ p3)))))) → True))) → (((False → (False ∨ p2)) → p4) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257975281523799809166564245228 : ((p4 ∨ p1) → ((((p5 → p4) ∧ (((p3 ∧ ((True ∧ p2) ∧ True)) → (False → False)) → p3)) ∨ (p2 ∧ ((False → (True ∧ p1)) ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_152022237123971830034756808159 : ((((p2 → (((p2 → (p3 ∨ p4)) ∧ p3) ∧ p3)) ∨ p4) ∧ (True → ((p3 ∨ (p1 ∧ p3)) ∧ (p2 ∧ True)))) → ((p2 ∨ p3) ∧ (p5 → p2))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h22 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h24 := h16 h23
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51979464597063659795130857166 : ((((p5 ∨ False) ∧ ((p1 ∨ ((p5 → p2) ∧ p2)) → (((p3 → p2) ∨ p1) → p4))) ∨ (((p3 ∨ False) ∧ p1) ∧ ((p2 ∧ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135158790865554716799847701261 : (((p5 → (((p3 ∧ p3) ∨ ((False ∧ ((p3 → p1) → p4)) ∨ (((False ∨ p2) ∨ p3) → p4))) ∨ p5)) ∨ (p2 → p1)) ∨ ((p4 ∧ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47969651362578915744555888296 : ((((((((((p3 ∧ (p5 ∨ p2)) ∨ True) ∧ (p1 ∨ p1)) ∨ True) → p3) ∧ p5) ∧ p2) ∨ (p3 ∨ ((True ∨ p3) ∧ p3))) → (p2 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638198208344209509609922984528 : ((((((True → (p1 → True)) → (False → (True → p1))) → (p1 ∨ ((((p4 ∨ p5) → p5) ∧ True) ∧ (((True ∨ p1) → p1) → p5)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197921523874810496100119621019 : (((p5 ∨ (False → p5)) → ((True ∧ p4) ∨ p1)) ∨ ((p1 → (p3 → (True → (p2 → True)))) ∨ (((p3 ∧ (p1 ∨ (False ∧ p1))) ∧ p1) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205489934395571523228081628033 : (((p1 ∧ p1) ∧ (p3 ∧ (True → p4))) ∨ ((p5 → (((p5 → (p2 ∧ ((p2 ∧ p3) → p2))) ∨ (True ∧ p3)) ∨ p5)) → (p5 → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328118988846215845926608150704 : (True → (((((p2 ∧ (False → (True → p4))) ∨ p1) ∨ (True → ((True → p2) ∨ p1))) → ((p2 → (False ∨ False)) → p4)) ∨ (False → (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204431873887666693108579847101 : (((((p1 ∨ p2) ∧ True) ∧ p4) ∨ p1) ∨ ((((p5 ∧ ((((p4 → p3) ∧ p3) ∧ ((p4 ∨ (p5 → p3)) ∨ False)) ∨ p4)) ∧ False) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164599921773440080796931590998 : ((((p2 → p4) → ((True ∨ ((p5 ∧ p1) ∨ p2)) ∧ (((p3 → p4) ∧ False) ∨ p3))) ∧ p1) ∨ (p3 → (True ∨ (p2 → (p1 → (p3 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42278941852598300039926014878 : (((p1 ∧ (False ∧ (p5 → (((((p4 → (p3 → (p2 ∧ p1))) → ((p2 ∨ p3) ∧ True)) → p1) ∨ True) ∨ (True ∨ (p4 ∧ False)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259192761500135330091864236981 : ((False → False) → ((p3 → ((((p4 ∨ (((p3 ∨ (((p4 ∨ False) ∨ p4) ∨ p3)) → p3) → p4)) ∧ True) ∨ p3) ∨ ((p5 → p3) → False))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51239072272081836465190287430 : ((((p5 → (p4 ∧ True)) ∧ (((False ∨ (p3 → ((p2 ∨ p1) ∧ p2))) ∧ (p2 ∨ p5)) → p5)) ∨ ((False ∧ (True ∧ (True → p1))) → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_69259266865336087897779442489 : ((p5 → ((p5 ∧ True) ∧ ((((((((True → (True ∧ (p3 → (p4 → False)))) ∨ p4) ∨ p4) ∨ (p3 ∨ False)) → p5) → p4) ∨ True) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190953905453264349261145571957 : (((p5 ∧ (p2 ∨ (p5 ∧ p3))) ∧ (p4 → (p2 ∨ p1))) ∨ (p1 ∨ (True ∨ (((False ∨ ((((p3 ∨ p1) → p4) → p1) ∧ False)) ∧ p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123631576975074463029185335063 : (((((p3 ∨ ((((p2 → p2) → (p3 ∧ p3)) ∧ p3) ∨ p4)) ∨ (True ∧ p3)) ∨ True) → (p3 ∧ (((p4 ∧ p3) ∨ p2) ∧ p4))) → (p5 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ ((((p2 → p2) → (p3 ∧ p3)) ∧ p3) ∨ p4)) ∨ (True ∧ p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335770690140328336645719779994 : (p1 → ((((((p2 → (p2 ∧ False)) → ((p4 ∨ (p5 ∧ (True → (False ∧ True)))) → ((p1 → p2) ∧ p2))) ∨ p5) ∨ p5) ∨ (p2 → p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164933066405297160986580187770 : ((((True ∧ ((p3 ∨ False) → (True → ((((False ∧ False) ∧ p4) ∨ p1) ∧ p3)))) ∨ p5) → p3) ∨ (p4 → ((False → p1) ∨ ((p2 → p2) ∨ True)))) := by
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
theorem thm_5_vars_61303645472063706678562747942 : ((False ∧ (p1 → ((p3 → ((p5 ∨ (((False ∨ p3) ∧ p1) ∨ ((p5 ∧ False) ∧ p3))) → (p4 ∨ ((False → (p4 ∨ p3)) ∨ False)))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157309134215767635358052675068 : (((p1 ∧ ((((False ∧ True) ∧ ((p1 ∨ p4) ∧ (p4 ∧ (p5 → p1)))) ∧ p4) → (True → p5))) → p5) ∨ (True ∨ ((p4 ∨ p3) → (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233815390063705243553599487806 : ((p3 ∨ (p3 → p5)) → ((p5 ∧ ((p3 → (p1 ∨ True)) ∨ (((p4 ∧ p2) ∨ p5) → (p4 ∧ p2)))) → ((p5 ∧ p3) ∨ ((True → p5) ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161022275576439032489124752348 : (((True → (p2 ∨ p3)) ∨ ((p5 ∨ ((p2 ∨ p2) → p4)) ∧ (p5 ∧ (False → (p5 ∧ (False ∨ True)))))) → ((p1 → (p2 ∧ p4)) ∨ (False → False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h6.left
      let h13 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138018554754757239121792779969 : ((True → ((True → (((p5 ∨ p3) ∨ (((True → (p1 ∧ p1)) → p5) ∨ ((p2 ∧ p3) ∧ p3))) ∨ (p1 → True))) ∨ p2)) ∨ ((p2 ∨ False) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123915288374747786637162601813 : ((((p1 ∧ ((p1 ∨ ((True → p1) ∨ False)) → (False → p1))) → False) ∧ ((p1 ∨ p2) ∧ (p3 → ((p4 ∧ (p5 ∧ p3)) → p2)))) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∧ ((p1 ∨ ((True → p1) ∨ False)) → (False → p1))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h7
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246522686532713259423950219700 : ((p5 ∧ p1) ∨ ((False → ((False ∧ (p2 ∧ p1)) ∨ True)) ∧ (p4 → (((p3 ∨ ((((True → p5) ∨ (False → False)) → True) → p5)) ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347513735259062895136488945253 : (p3 → (((((p3 ∧ p2) → p3) ∨ p1) → False) → ((False → (True ∧ p3)) → (((p1 ∨ True) ∧ p5) ∨ ((p4 ∧ (p1 ∨ True)) ∨ (p1 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ p2) → p3) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52159330257673360424562423480 : ((((((False ∨ p2) → p1) ∧ (((False → p1) ∨ True) ∨ p1)) → ((p1 → False) ∧ p2)) → (p2 ∧ (((True ∧ (p1 → False)) → p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112643414252843475007859547870 : ((((p4 ∨ ((p4 ∧ (p4 ∨ True)) → (p5 ∧ ((True → (p2 ∧ ((p3 ∧ p4) ∨ p4))) ∧ (True → p1))))) → (p4 → p2)) → p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8250925702612554231886834015 : ((((((((p2 ∨ (p4 → p5)) ∨ False) ∧ p5) ∨ (((p1 → p5) ∧ ((p5 ∨ p1) → (p4 → (p1 ∧ p5)))) ∧ p1)) ∨ p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140702788076972211076401857197 : (((((p2 → ((True ∧ True) ∧ p3)) ∨ p5) ∨ (True → (True → (p3 → p3)))) ∨ (p2 ∨ (((True ∧ False) ∧ p5) ∨ p2))) → ((False ∨ p3) ∨ True)) := by
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678178171502738594109143402107 : (((((p1 ∨ ((p3 ∨ p5) ∨ (p5 → ((p4 ∨ True) ∧ (p5 ∧ p4))))) → (p5 ∨ ((p3 ∨ p1) ∨ p5))) ∨ ((False ∨ (False → p3)) ∨ p3)) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314258223783403228016411966021 : (p3 ∨ (((p4 ∨ ((False → p2) ∨ p2)) ∧ (p4 → ((p3 ∨ (((False ∧ p5) → False) → (p1 ∧ p5))) ∨ (p1 ∨ True)))) ∨ ((False ∧ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117120624167193629739770687054 : (((p3 → p5) → ((True → ((False ∧ p1) ∧ p2)) → ((p4 ∨ False) ∧ (p5 → (((False ∨ p1) ∨ (p5 ∧ (p5 ∨ p3))) ∧ p4))))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138334277356845714811773485042 : ((p3 → (p2 → (((p4 ∨ p1) ∨ False) ∨ ((((((p1 → p4) → (p3 ∧ (p2 → p5))) ∧ p3) → p3) ∨ p5) → p5)))) ∨ (True ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119205230635482229482211043737 : ((p2 → (((p4 ∨ p1) → (((False → p3) ∧ ((True → p2) ∧ True)) → (True ∨ False))) → ((True → p5) ∧ ((True ∧ p2) ∧ p4)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209442083481601467062523495111 : ((p2 → (p4 ∧ (p4 ∧ (p1 ∨ p1)))) → (((p3 → p3) ∧ ((p5 → p2) ∨ p5)) ∨ (((p3 ∨ False) → True) ∨ ((p3 ∨ (p5 ∧ p1)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309591222761217324671901899152 : (p2 ∨ ((p5 ∨ (((True ∧ p3) ∧ p5) ∨ (p4 ∨ (True ∨ (((p4 → p5) ∨ p1) ∨ (p4 ∨ (True ∨ (True ∨ True)))))))) ∧ (True ∨ (False ∧ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165362765053205708370006243528 : (((p5 → (p5 → ((p2 ∨ False) ∧ ((p5 ∧ (p4 → False)) ∧ False)))) ∧ ((True ∨ p3) ∨ p2)) ∨ ((p4 → (((p1 ∧ False) ∨ p5) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42726151399355106118037995882 : (((True → ((((p3 ∨ p5) ∨ ((p5 ∧ ((p3 → p4) → p5)) → (((p1 ∨ ((False ∨ p3) ∨ p5)) → p1) ∨ p3))) ∨ p2) ∨ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625811514562776137343863471643 : ((((p1 → (p4 ∨ ((p1 ∧ ((False ∨ ((p4 ∧ True) ∧ True)) ∧ (((False ∨ p3) → (p4 → (False ∨ p3))) → p2))) ∨ (p3 ∧ p3)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_248665150800240269449556330034 : ((p3 ∨ p1) ∨ (False ∨ (((((p3 ∨ p5) ∨ True) ∧ p4) ∨ (((((True → (False ∧ p3)) ∨ p1) ∧ (False → (p5 ∨ False))) ∧ p1) → True)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305160183297732549122883469941 : (p1 ∨ ((((p2 ∧ (False ∨ ((((True ∧ p2) ∧ p2) ∧ False) ∧ p3))) ∨ ((p3 ∧ (p3 → p4)) → p1)) ∨ True) ∨ ((p5 ∧ (p2 ∧ False)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355907521664526000183851912015 : (p5 → (((((((False ∨ (p5 ∨ False)) ∧ ((False ∧ False) ∧ (((p5 ∧ p5) → p2) → False))) ∧ p1) ∨ p3) ∨ p4) → p2) → ((True ∧ p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((((False ∨ (p5 ∨ False)) ∧ ((False ∧ False) ∧ (((p5 ∧ p5) → p2) → False))) ∧ p1) ∨ p3) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648050359454057560464547735932 : ((((((p2 → (p3 ∨ ((p1 ∧ (p4 ∧ p1)) ∧ False))) ∧ (p5 → ((p4 → False) → (((False ∨ p2) → False) → p1)))) ∧ True) ∧ (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749941442872223806605247825951 : (((True ∧ ((((p2 → (False → p4)) ∧ ((False → p1) → ((p3 → p4) ∧ (p5 ∧ ((p2 ∨ p4) → ((p1 ∨ p1) ∨ p5)))))) → p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158396114209873795264224257653 : (((p4 → p1) ∧ ((((True ∧ False) ∨ False) ∧ (False ∧ (((p2 ∨ (p2 ∨ p5)) → False) → False))) ∧ False)) ∨ ((True ∨ True) ∨ ((False ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336125984722936178686388323942 : (p1 → (((((p2 ∨ ((p3 → p4) ∧ p4)) ∧ p5) ∧ (((((True ∧ (p3 → p3)) ∨ True) ∧ False) ∧ ((True ∨ p3) → p2)) ∧ True)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738551176853443145343458688339 : ((((p1 ∧ p5) ∨ ((False ∨ ((((p3 ∨ p3) ∧ ((p1 ∨ p3) ∧ (((p3 ∨ (True ∧ p3)) → True) ∨ p2))) ∨ True) ∧ p2)) ∨ (True → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651991106946156760815684008854 : ((((True ∧ ((False ∧ p2) ∧ (p1 ∨ (((p3 ∨ (((p3 ∨ True) ∧ (p4 → (True ∨ (p2 → p5)))) ∧ p3)) ∧ p5) ∨ p4)))) ∧ (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621681031677996336456916991072 : ((((False ∧ (p5 ∨ (((((p1 ∨ (True ∧ (False → ((p1 ∨ (p3 ∨ False)) → False)))) → p1) → (p1 → (p3 ∧ p2))) ∨ p4) ∧ True))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_720027969715740628661619755729 : ((((((p1 ∨ False) ∨ p3) ∧ p3) → ((((((p5 → False) ∨ p4) ∨ (True ∨ True)) ∨ p2) → (((False ∧ p3) ∨ p3) ∨ (p4 → p5))) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172187669681254138758622907074 : (((p3 → (p2 ∨ (p5 ∨ ((p2 ∨ (False ∧ p4)) ∨ False)))) ∨ (True ∧ (False → p5))) ∨ ((p5 → (False → False)) ∧ (((p1 ∧ True) ∧ False) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65918968036631088556610146784 : ((p4 ∨ (p4 ∧ ((p4 ∧ (p2 → (((((False ∧ p5) ∨ True) ∨ p1) → False) → (p3 ∨ True)))) ∨ (((False ∨ True) → (False ∧ True)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259007483829928826606258173095 : ((True → p4) → (((((False ∨ (True ∨ (False ∧ p5))) ∧ ((p4 → True) ∨ ((p2 → p1) → p2))) ∧ p5) ∨ (((p1 → False) → p5) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117052863273421223233108579816 : (((p4 ∨ p4) → (((True ∧ p5) ∨ ((p2 ∧ True) → p2)) → (((((p5 ∨ p3) ∧ p2) ∨ (p5 → p5)) ∧ (p4 → True)) ∨ p2))) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60889470589303380742626229755 : ((True ∧ (p3 → (((((p2 ∧ (p5 ∨ True)) → (p1 ∧ (p3 ∧ (p1 ∨ (True ∨ p4))))) → (False → p1)) ∧ (p1 ∧ (p1 ∧ True))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118249880274178966433865065534 : ((p1 ∨ ((p4 ∧ (((((p1 ∨ (True ∧ (p2 ∨ (p4 ∧ p1)))) → (True ∨ True)) ∨ False) → False) ∧ p2)) ∧ (p1 ∨ (p1 → p1)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199154212268479876641709026995 : ((((p4 → True) ∨ ((p3 → p2) ∧ p4)) ∧ p2) → ((((((((p2 ∨ p1) → (p3 ∨ p1)) ∨ p5) ∨ (p5 ∨ p1)) → False) ∨ p2) ∧ True) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668755265435487082675433100931 : ((((((((p4 → p1) ∧ p3) ∨ ((((p2 → False) → (p2 ∧ (p1 ∨ True))) ∧ p5) ∧ (p2 → p4))) → False) ∨ True) ∨ (p5 ∨ (p2 → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39698091811372541937167566348 : (((p4 ∨ (p3 ∧ ((False ∨ ((p4 ∨ (p4 ∨ (p4 ∨ p1))) ∧ (((True ∧ p3) ∨ p1) ∨ p2))) → ((p3 ∨ True) ∧ (True ∨ p4))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50719380213726941719232397636 : ((((p3 → p4) ∨ ((p4 ∧ ((p5 ∧ (p1 ∨ (p5 ∨ (p1 ∨ (p4 → (True → True)))))) → p3)) → False)) → (p5 → ((True → p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650785457895320542670180191390 : ((((((((p4 ∧ False) → p2) ∧ (p2 ∧ p4)) ∧ p1) ∨ (((p1 ∧ p1) ∨ (False ∨ True)) ∧ ((p1 ∧ p1) → (p4 → p4)))) ∧ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58810702688040862165767184339 : (((p5 → p3) ∧ ((((p1 → (True ∧ (p1 → p3))) → (p2 ∨ (p1 ∨ p1))) ∨ (p2 ∨ ((True → p2) ∨ (p1 → (True ∨ p3))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317053536217927307786623035148 : (p3 ∨ (p4 → ((((p1 ∨ (((p2 ∧ (p2 ∧ ((False ∧ True) ∧ p2))) ∨ False) ∧ p4)) → True) → p2) ∨ (True ∨ ((p1 ∧ (p1 ∨ True)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119110442335633367765030022005 : ((p1 → ((True → True) ∧ ((p3 ∧ (p1 ∧ ((p3 ∨ False) ∨ (((p2 ∨ p5) → (False ∨ ((p1 ∧ p2) ∧ p3))) ∨ p4)))) → p4))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113362703183949020245906916440 : (((p5 ∧ (p1 ∧ (((p2 → True) → True) ∧ (p1 → (p4 ∨ (p1 ∧ ((((p2 ∧ p1) ∧ p5) → False) ∧ True))))))) ∧ (p3 ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57067145586255050769367581821 : (((p5 → (True ∨ False)) ∧ ((((((p4 ∨ p1) → ((False ∧ p5) → p1)) ∨ True) → (True ∨ (False ∨ ((p5 ∧ p4) → p1)))) ∨ False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111663567425515131185923585099 : ((((False ∨ ((p2 ∨ ((p1 ∧ (((p4 ∧ ((True → p3) → p3)) ∧ (p2 ∧ False)) → p5)) → False)) ∧ (p4 → False))) ∨ p3) ∨ True) ∨ (True ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183951722752272524351848092105 : (((p4 ∨ (p5 ∧ (p1 → (p2 ∧ (p5 ∧ (p3 ∨ p1)))))) ∧ p4) ∨ (p2 ∨ ((((p1 ∧ p3) ∧ (False ∨ p5)) → ((True ∧ p3) → p3)) ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66634767761269672713013628440 : ((True → ((True → (p4 ∧ (p1 ∨ (p4 ∨ (((p4 ∧ p5) ∨ False) ∧ (p3 ∧ False)))))) → (p3 ∧ ((p2 ∨ (p5 ∨ p3)) → (False ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245115189256463078029517828916 : ((p2 ∧ True) ∨ ((((((p2 ∨ ((((p5 ∧ True) → False) → (p4 ∨ p5)) → p3)) ∨ False) → p4) ∨ True) ∨ (p4 ∨ p4)) ∨ ((p2 ∨ p1) → p1))) := by
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
theorem thm_5_vars_253930753346485039130800697534 : ((p1 ∧ p4) → ((p1 → (((p1 ∧ False) ∨ (p1 ∨ True)) ∧ p5)) ∨ ((((p2 ∧ ((p4 → p1) → ((p5 → p4) ∧ False))) ∨ p3) ∨ p4) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327872665629097623964505057529 : (True → (((p5 → p3) → (((p5 → p2) ∧ ((p2 → ((p4 → (True → p1)) → p4)) → (True ∨ p4))) → ((p4 → p1) ∨ p2))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225517690970315064466596171950 : (((p5 ∨ p5) ∧ False) ∨ (p4 → ((p1 ∨ p2) ∨ (p2 → (((p3 ∧ True) → (((((p2 ∧ p3) ∧ p3) → False) ∧ (True → False)) → p4)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59991596306376219721951862861 : (((False ∨ p3) → ((((p3 ∧ p4) ∧ (True ∧ p5)) ∧ ((p3 ∧ p1) ∧ (False ∨ (((((p4 → p1) → p5) → p4) → False) ∧ p3)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803800057905212200430208572794 : (((p3 → ((((p3 → (p3 ∨ ((False ∨ p4) → (p5 ∧ (((((p5 → p4) ∨ p4) ∨ True) → p3) ∨ p1))))) → p5) ∨ True) ∨ (True ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40955184989844842830967359358 : (((((((p5 ∧ ((p5 ∨ p2) ∨ (False ∧ p3))) ∧ True) ∧ (p1 ∨ ((p5 ∧ p3) → p1))) ∨ ((p2 → True) ∨ p5)) ∨ (p1 → False)) ∨ p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207952544665240732521273259008 : (((p3 → (False ∨ True)) ∧ (p4 ∧ p2)) → ((((p4 ∧ p3) ∧ p5) ∧ ((((p4 → p3) → False) → (((False ∨ p2) ∨ p3) ∧ p5)) ∨ True)) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173934525752700272083496391076 : (((((p1 ∧ p5) ∨ (p2 → (p3 ∨ (p5 ∨ (p3 ∨ True))))) → (False ∧ True)) → p1) → (((((p4 ∨ p3) ∧ p5) ∧ p2) ∧ (p4 ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339484272252178665191281557060 : (p1 → (False ∨ ((False ∨ (False ∧ ((((True → (((p1 ∨ p2) → (p4 ∧ p1)) ∧ ((p1 → p5) ∨ p2))) → p5) ∧ (p2 ∧ p2)) ∧ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2374977495183419664093064518 : (((p5 ∧ (p1 → p4)) ∨ ((((p2 ∨ p1) → True) → p4) ∧ p5)) ∨ (p1 → (False → ((p3 ∧ p2) ∨ ((p4 ∨ p5) ∨ (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727918234647895328896507717208 : ((((p2 ∨ (p3 ∨ p2)) ∨ (((p3 ∧ p2) ∨ p3) ∨ ((True → (True ∧ (((p1 → p2) ∧ p5) ∨ ((p2 → p1) → p5)))) ∨ (True ∨ p1)))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638577702751363849461133357680 : (((((p4 ∧ (p3 → (p3 ∧ (p2 → p4)))) ∨ (((p5 ∨ True) ∧ ((False ∨ (False ∨ False)) ∨ ((p3 ∨ p5) → False))) ∧ (p5 → True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52836940949734387529660590600 : ((((p5 → (p1 ∧ p1)) → ((((p1 ∨ (False → True)) ∨ p4) ∧ p3) ∧ False)) → (p1 → (p5 ∨ (p5 ∧ ((p4 ∧ (p3 ∨ False)) → p2))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (p1 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



