variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164929302989801930342738746676 : ((((((p1 ∨ False) ∨ (p2 ∨ True)) → ((p4 → p4) ∧ (p5 → (False → False)))) ∨ p1) → p5) ∨ (False → (p2 ∨ (True ∧ ((p5 ∨ True) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597535699160914708975279398837 : (((((p3 ∨ (True ∧ (p2 ∧ False))) ∨ (((False ∧ p3) ∧ p1) ∨ (False → ((p5 ∨ ((p5 ∧ False) ∧ ((p2 ∨ p2) → p5))) ∨ False)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138358773975808476807743004738 : ((p4 → (((((False ∨ False) ∨ p4) → p3) → (((p4 → p5) → p3) ∧ ((p2 → (p3 ∧ p3)) ∨ p4))) ∨ (p4 ∧ p1))) ∨ ((True ∨ p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47266255465442453359557974301 : (((((p4 → (True ∨ p3)) ∧ False) ∧ ((p4 → p5) ∨ ((((True ∧ p2) ∧ p3) ∧ p4) ∨ ((p1 → False) ∧ (p2 ∨ p5))))) ∨ (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640276501571248643874602678296 : (((((False ∨ (p3 ∧ p1)) → (p5 ∧ ((True → p5) ∨ ((p5 ∧ p4) → (((p2 ∨ p1) ∧ False) ∧ (((p2 ∧ False) → p2) ∨ p4)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660298548943202973863611870339 : (((((p2 ∧ ((((p3 → False) → p2) → ((p5 ∧ ((False ∨ (p2 ∨ p1)) ∧ (True ∨ p5))) ∨ (p1 ∨ p5))) ∨ p3)) ∨ p5) → (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113963041343014543719849478888 : ((((p3 → p4) → (((True → (p3 ∧ (((p3 → False) ∨ p1) ∨ (False ∨ False)))) → p5) ∧ (True ∨ False))) ∧ ((True → p1) → p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135946498639857754087643740585 : ((((p5 ∨ (((p3 → True) ∨ p2) → p4)) ∨ (p3 → True)) ∧ (((((False ∨ (p2 ∧ p3)) ∨ p4) ∨ p1) → True) → p5)) ∨ ((True ∨ False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89189101739079286152184166679 : ((((p1 → p5) → True) ∧ ((((False → p1) ∨ ((False ∨ (p2 ∨ p1)) → p1)) ∧ p5) ∧ ((p4 → p2) ∧ (True ∧ (p1 ∧ (False ∨ True)))))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209271322128568574241486274306 : ((True → (((True ∨ p1) → p5) ∧ p3)) → ((True ∨ p5) → (p2 → (((p5 → (True ∨ p4)) ∧ (p4 → ((p5 → False) ∨ (p5 ∨ p3)))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122066172873968499369719972920 : (((p2 → ((p1 ∧ p4) ∨ ((((p2 → p1) → p3) → ((False ∨ (p4 ∨ (p4 ∨ p1))) ∨ (False ∨ p2))) ∨ (p5 ∨ True)))) → False) → (p2 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p1 ∧ p4) ∨ ((((p2 → p1) → p3) → ((False ∨ (p4 ∨ (p4 ∨ p1))) ∨ (False ∨ p2))) ∨ (p5 ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354781618793650846432420143147 : (p5 → (((p4 ∧ (((False ∧ p4) ∧ (False ∨ p3)) ∨ p4)) ∧ ((((p1 ∧ (True ∧ False)) → ((p3 ∧ True) → p3)) → p4) ∨ (p1 ∨ p4))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255423797899043356327014729703 : ((p5 ∧ p1) → (((p3 ∨ ((p2 ∨ (p3 ∧ ((p4 ∨ p4) ∧ (p2 ∧ p4)))) ∧ (((p4 → (p2 → p2)) ∧ p4) → p5))) ∧ (p3 → True)) ∨ p5)) := by
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
theorem thm_5_vars_353410783925299157415766199494 : (p4 → (p1 ∨ (((((p2 → (p5 ∨ p4)) → False) ∧ (((p5 → (True ∧ ((p5 ∧ p5) ∧ (True → (p4 → p4))))) ∨ False) ∨ p2)) → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (p2 → (p5 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h7
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p2 → (p5 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h12
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82197677874078621650967909862 : (((p5 → (((p3 → ((True ∧ (p5 → True)) ∨ p4)) → (p1 ∧ (p2 ∨ ((p3 → (p3 → p5)) → p5)))) ∨ p5)) → (True ∧ (True ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p3 → ((True ∧ (p5 → True)) ∨ p4)) → (p1 ∧ (p2 ∨ ((p3 → (p3 → p5)) → p5)))) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165540104204710621940631923686 : (((((p3 ∧ p5) ∧ (p4 ∨ (p5 → False))) ∨ False) ∧ (False ∧ ((p3 ∨ (p4 ∧ p4)) ∨ p1))) ∨ ((p2 ∧ (p1 ∧ p4)) ∨ (True ∨ (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147434841946271682791621623609 : ((((True ∧ p5) ∧ (((p2 ∧ ((p2 → ((p3 ∨ (p2 → True)) ∧ p5)) → (p5 → p5))) ∨ p1) → p5)) ∨ p1) ∨ ((False ∧ (True → False)) → p2)) := by
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
theorem thm_5_vars_218568980148833130813815210436 : (((p1 → False) → (False ∧ p4)) → (((((p4 ∧ (p3 → ((True ∧ p1) ∧ p4))) ∨ ((False ∧ p5) ∧ p3)) → p4) ∧ p4) ∨ ((False → True) ∨ p1))) := by
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
theorem thm_5_vars_342322817390603384230485233353 : (p2 → ((((((False → (p1 ∨ (p3 ∧ p1))) → p3) ∧ p5) → p2) ∨ (((p5 ∧ p3) ∧ p2) ∨ p3)) → ((p4 ∧ False) ∨ (False → (p5 ∧ p2))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46136754452195463896135893618 : ((((((p5 ∨ (((True → ((((p5 → True) → p4) → (False ∧ p4)) ∨ p4)) ∨ p2) ∧ (p4 → False))) → p4) ∨ p4) → p5) ∧ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233884358922305487673311007985 : ((p4 ∨ (p2 ∨ False)) → ((((p5 ∨ p5) ∨ ((p5 ∨ True) → (p2 ∨ (p1 ∨ p5)))) ∨ ((False ∨ ((False ∧ p4) ∧ p3)) → p5)) ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51210543242153001827039215084 : ((((((True → p1) ∧ p1) ∧ ((False ∨ p5) ∨ p4)) ∨ ((p3 ∨ p2) ∨ (False ∨ (p3 ∨ True)))) ∨ (((p2 ∨ p2) → (p2 ∧ p2)) ∧ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253942218146666101004304567739 : ((p1 ∧ p4) → (True ∧ (((p5 → p3) → ((p2 ∨ ((p4 → (((True ∨ True) → ((p1 → p4) ∧ p1)) → p3)) ∨ p3)) ∨ (p5 ∨ p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265059015797057622709755052539 : (True ∧ (True ∧ ((True ∨ True) ∧ ((((p2 ∧ p3) ∨ ((True ∧ (p1 → p3)) ∧ (p2 ∧ p4))) ∨ (((p2 ∧ p3) → p2) → (p4 → True))) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_111684329831233567012119284372 : ((((((((p1 → p2) ∨ (p5 ∨ ((p1 ∨ p5) ∨ (p1 ∨ p3)))) → ((p3 ∨ p1) → (True ∨ p4))) ∧ p3) ∨ p4) → p5) ∨ p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608663813385119769348102959424 : (((((((p5 ∨ ((p3 → p1) → p4)) ∨ (p1 → (((p3 ∨ p4) ∧ p4) ∨ (p5 → ((p5 → True) → p3))))) ∨ (p5 ∨ p4)) ∨ True) ∨ p2) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_136237806371258749921270514539 : ((((p5 ∧ p1) ∨ (p4 → (p1 ∧ p2))) ∨ ((True ∨ False) ∧ ((((True ∨ p3) ∧ (p4 → (False ∧ p3))) → p3) ∧ p2))) ∨ ((p4 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147278143441421106816154497262 : ((((((p4 ∨ p3) ∨ p4) → (((False ∨ (p5 ∨ ((p1 → (p3 ∧ p1)) ∨ p5))) ∧ True) → p2)) ∨ p5) ∨ False) ∨ ((False → True) ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115435055845208482333219770782 : ((((True ∧ (p3 ∨ ((p2 ∧ p1) → p2))) → p2) ∨ ((p4 ∨ ((((p1 ∨ p4) ∧ False) → p3) ∧ (True ∨ (p4 ∧ True)))) → p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244737838817651042706846140144 : ((p1 ∧ False) ∨ ((False ∧ ((p4 → (p2 ∨ p2)) ∧ (((True → (p3 ∧ (p1 ∨ p5))) → (p2 ∨ (True ∨ (p2 → p5)))) ∧ (True ∨ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103219511541302177044000015010 : (((p1 ∧ ((False ∨ p2) ∧ (((p5 ∨ ((p5 ∨ ((p5 ∨ p5) ∧ True)) → ((p3 → p3) ∧ True))) ∨ True) → (p4 ∨ True)))) ∨ True) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156911540153518654010788280362 : (((((True ∧ ((((False → p4) → False) ∧ (p3 ∧ True)) ∧ (p2 → p4))) ∧ (p3 ∨ p2)) → False) ∨ p3) ∨ (p3 → (((True ∨ p2) ∧ p4) ∨ p5))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h13
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h17 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h19 := h8 h17
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134798056701891133258460084810 : (((p3 ∧ (p2 ∨ (((p3 ∨ (((p2 ∨ True) → (((p4 ∨ False) ∧ p5) ∧ (p3 → p4))) → p5)) ∨ False) ∨ p1))) → p1) ∨ (True ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585813241668525716800610539401 : ((((((p1 → (((p3 → (p3 ∧ p1)) → (((True ∧ p5) ∧ (p1 → (p2 → True))) ∨ ((p4 ∧ False) ∨ p2))) ∨ p5)) → False) ∧ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117928235447282339905301370657 : ((p5 ∧ ((p3 ∧ p5) ∧ (((True → p1) → ((((True ∨ p2) ∨ p3) → p1) ∨ p5)) ∧ (((p2 ∨ (False → p4)) → p1) ∨ True)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117414697034013846282469779212 : ((p1 ∧ (((p1 ∧ True) → ((p5 ∧ ((p5 → ((p2 ∧ (False ∧ True)) → (False ∧ p4))) → (p3 ∧ p4))) ∨ p5)) ∧ (p1 → True))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179131657955082247685169844338 : ((p1 ∧ (((p2 → (p1 ∧ p2)) → p4) → (False ∧ ((True ∧ p5) ∨ p2)))) ∨ ((p1 → (p1 ∨ (True ∧ p4))) ∨ ((p3 ∨ (False → p5)) ∧ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315516880448233682220887826056 : (p3 ∨ ((p4 → (p3 → p4)) → (p5 → (((False ∨ ((False ∨ p4) ∧ p2)) ∨ (p3 ∨ (((p5 ∨ p2) → p4) → (p1 → (p1 ∧ p4))))) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200778822222957425403270047176 : ((p4 ∧ ((p1 ∧ p3) → ((p2 ∧ p4) → p5))) → (((p3 → ((p2 ∨ (p1 ∨ p3)) → True)) → ((p3 → p1) → p2)) ∨ (True ∨ (p3 ∧ p1)))) := by
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
theorem thm_5_vars_45323790441959607573747056963 : (((p3 ∧ ((p3 ∧ (((p2 → ((p2 → True) → False)) → False) ∨ p1)) ∨ (p2 ∧ ((False → True) → (((p5 ∧ p5) → p5) ∧ p4))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43238759173421730007418492324 : ((((p3 ∨ ((p5 → False) ∨ (p5 ∨ ((True ∨ p5) → ((((p2 → ((p4 → p4) → False)) → (p2 ∧ p1)) ∨ False) → False))))) ∧ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198440270206917425505726882574 : ((p5 ∧ ((((p2 → p2) ∧ p5) → True) ∧ False)) ∨ (((False ∧ ((p3 → p3) ∧ p2)) ∧ p1) ∨ (p5 ∨ ((False ∨ p2) ∨ (False → (p2 ∨ p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224187099923828536598422202614 : ((True → (True ∨ p3)) ∧ ((p5 ∧ (p3 ∨ (p5 → p2))) ∨ ((False ∨ ((p3 → p5) ∨ (p5 ∨ True))) ∨ ((True ∧ (True ∧ (p3 ∧ p1))) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_760848497553417860401348636249 : (((p2 ∧ (p3 ∨ (((p3 → (p2 → True)) → ((p2 ∨ p3) ∧ (p3 → (((p2 ∨ False) ∧ (p4 ∧ p2)) ∨ p2)))) → (p1 ∨ (p5 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136338396120423736266684603897 : (((p2 ∧ (p4 → (False ∧ p4))) ∧ ((p5 ∨ (((p1 ∨ (p3 ∨ (p5 → True))) ∨ False) ∧ p2)) ∧ ((True ∨ p4) ∨ True))) ∨ ((p3 ∧ False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165745041127019464217792791452 : ((((False → p1) ∧ (p4 ∧ p5)) ∨ (((p1 ∨ True) → (p3 → ((p3 ∨ True) ∧ False))) ∨ True)) ∨ ((p4 ∨ p3) → ((False ∧ False) → (p1 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259819129820342215740300503655 : ((p1 → p3) → ((((True ∨ ((p1 ∨ p2) → False)) ∨ p3) ∨ ((False ∧ p2) ∨ p2)) → ((((False ∨ (True ∨ p5)) → False) → p5) ∨ (p2 → p2)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343239456514232052112245342221 : (p2 → ((p1 ∨ (p4 → p1)) → (((p2 ∧ (p4 ∨ (p2 ∧ p1))) → (p5 → (True ∧ p2))) ∧ ((((p1 → True) → p3) ∧ (False ∧ p5)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186332437914885850293218495713 : (((((p5 ∨ p5) ∧ (p2 ∧ True)) ∨ ((False ∨ p5) ∨ True)) → False) → (p5 ∨ (((p4 ∨ (p3 ∧ (p4 ∨ ((p2 → p2) ∨ False)))) ∨ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p5) ∧ (p2 ∧ True)) ∨ ((False ∨ p5) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746737618571973314630625551676 : ((((p3 ∨ p3) → (((((((p5 ∧ p5) → p1) ∧ ((True ∨ p2) ∧ p1)) ∧ (True ∧ (p3 → True))) → (True ∧ p4)) ∧ p3) ∨ (p1 ∨ p3))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604354365121794288785225267931 : ((((True → ((p1 → (p5 → p3)) ∧ (p3 ∨ (p5 → (((((p1 ∨ (p1 → (p5 → (p3 ∧ False)))) → False) ∨ p4) ∨ p4) ∧ p4))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308550412270464116742431708889 : (p2 ∨ (((((False ∨ p1) ∧ p3) → (p3 → (p5 → p1))) ∧ ((((p2 → (p4 ∧ ((p3 ∨ True) ∧ True))) ∧ p1) → (False ∧ p5)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51396264598161953427609058827 : ((((p5 → ((((p3 → (p2 → (p5 ∧ p2))) ∨ False) → ((True ∧ True) ∨ True)) ∨ p4)) ∨ p4) → ((((False ∧ p4) ∨ False) ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319216465228231028117006062155 : (p4 ∨ (((p3 → p5) ∨ ((((p4 ∨ ((p5 ∨ p4) ∨ p2)) → (False ∨ p2)) → True) ∨ (p3 ∧ p1))) → (((p4 ∧ p4) ∨ True) ∨ (p4 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109806373211183732064496505130 : ((p5 ∨ (((((p2 → p4) ∧ p2) ∨ (p2 ∨ p3)) ∨ (True ∧ (False → p2))) ∧ ((p4 ∨ p2) ∨ ((False ∨ p2) ∨ (True ∨ False))))) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387907155735253964929849964101 : (((((p5 → (True ∨ ((p3 ∨ (True ∨ (False → ((((p4 → (False ∨ False)) → False) ∨ p5) → p1)))) ∧ p3))) → (p1 ∨ (True ∧ True))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41157791286424001735606142600 : ((((p4 ∧ ((True → (p4 ∨ False)) ∧ (True → (False ∧ (True → (p4 → (p5 ∧ (p4 ∨ (p2 ∧ p5))))))))) ∨ (p1 → (p1 ∧ p3))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800269276337939381892319648149 : (((p2 → (((False ∧ (False ∧ ((p4 ∨ ((p2 ∨ True) ∧ p3)) → ((p3 ∨ ((p5 ∨ p5) → (p4 → p1))) ∨ p2)))) ∧ (True ∧ False)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111785701639447228522960762989 : (((((((False → True) → False) ∧ (True → (p4 ∧ (p4 ∨ p1)))) ∧ ((p1 ∨ (p4 ∧ p3)) ∨ (p5 → p2))) ∨ (p3 → False)) ∨ True) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173318765598276848278350073703 : ((p2 → ((((p3 ∧ ((True → True) ∧ p4)) ∧ p1) ∧ ((p1 ∧ p4) ∨ p4)) ∨ False)) ∨ ((((p1 ∨ p3) ∨ p5) → True) ∧ ((False ∧ True) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310042470967659959984993237292 : (p2 ∨ ((p2 ∨ ((((p1 ∨ ((p4 → p4) → p1)) → p4) ∨ p4) → (p5 → (p2 ∨ False)))) ∨ (p1 ∨ (((p2 → (True ∨ True)) ∨ p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60853664569615319262938508130 : ((True ∧ (p3 ∨ (p2 ∨ ((((False ∨ ((False → (False ∧ p5)) → (p5 ∨ (p3 ∨ ((p4 ∧ (p3 → p4)) ∨ False))))) ∨ p2) ∨ True) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197185666389059229830994864327 : (((((False ∨ p3) → (p1 → p4)) ∧ p5) → p1) ∨ ((((p4 → p2) ∨ p5) ∧ (True ∧ p5)) ∨ (p5 ∨ (True ∨ (p1 ∨ ((p4 → p1) ∧ p4)))))) := by
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
theorem thm_5_vars_328501605584717720653687565005 : (True → ((p1 ∨ ((((p1 ∧ (((p2 ∨ False) → p2) → False)) ∧ (p1 ∧ p4)) → False) ∨ False)) ∧ (((p2 → p1) → (p2 ∧ (True ∧ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : ((p2 ∨ False) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h9
  -- False on the left can always be used.
  apply False.elim h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266059169276090547860199410822 : (True ∧ (p2 → ((((((True ∧ (((p1 ∨ True) ∨ p4) → p4)) ∧ p4) → (p1 → p5)) → (p3 → ((p5 ∧ False) ∨ True))) ∨ (True ∨ True)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184480822731799304862954144552 : ((((((False ∨ (False ∧ p1)) → True) ∨ p5) → p3) ∨ (p4 ∧ p5)) ∨ (((((p5 ∧ True) → False) ∧ p1) → (((p4 ∨ p2) ∨ True) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706819542014827898075879051634 : (((((False ∧ (p5 ∧ ((False ∨ p2) ∨ p4))) ∧ p3) ∨ ((False ∨ False) → ((p5 → (p1 → (True ∨ (True ∧ True)))) ∨ ((p3 ∧ p5) ∧ False)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218047583235705048739342029570 : (((p2 ∨ p4) ∧ (p4 → p2)) → ((((p5 → False) ∧ p5) → ((p2 ∧ ((p1 ∧ p3) ∨ p1)) ∧ (p4 → (p3 → True)))) ∨ (False ∨ (True ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748122969121780678887879797316 : ((((p1 → p3) → ((p1 ∨ ((p2 ∧ (p3 → p4)) → ((p3 ∧ p4) → p3))) ∨ (p1 ∧ ((False → p2) → (False ∧ ((p4 ∧ p4) → p5)))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126684228624263345186691451410 : ((p4 ∧ ((((((p5 ∨ p5) ∧ (p1 ∨ (True ∧ (False ∨ (False → False))))) ∧ (((p5 ∨ True) ∨ True) ∧ p2)) ∨ p3) ∨ True) → False)) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p5 ∨ p5) ∧ (p1 ∨ (True ∧ (False ∨ (False → False))))) ∧ (((p5 ∨ True) ∨ True) ∧ p2)) ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14571154012635556424464441884 : ((((True ∧ (((True ∨ ((((p3 → True) ∧ (p4 → (False ∨ p2))) → ((p3 ∨ p2) ∧ p4)) → p4)) ∧ p4) → p1)) ∨ p1) ∨ (False ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304690007672347674537393265350 : (p1 ∨ (((((p1 → False) ∧ p4) ∧ (True → ((p2 ∨ p2) ∧ (p3 ∧ ((p4 → (p2 → True)) ∧ (p3 ∨ (p2 ∧ p2))))))) ∨ True) ∨ (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300830221401673302008726816529 : (False ∨ ((p5 ∨ (((((p3 ∨ p5) ∨ p2) ∧ False) ∧ False) → (p1 ∨ ((p3 ∨ p5) ∧ p2)))) → (p5 ∨ ((p2 → False) ∨ (False → (True → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54072320229759534899156932524 : ((((False ∧ (p4 → p2)) → (p1 ∧ ((p4 → p5) ∨ p2))) → (p2 ∧ (p1 ∧ (p4 → (False ∧ (p2 ∧ (p5 → (p2 ∨ (p3 ∨ p2))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116842731867460058236762397219 : (((True → p4) ∨ ((p2 → ((p4 → ((p2 ∨ p2) → p3)) ∨ (((p5 ∨ (True ∧ False)) ∨ ((p1 ∨ p2) ∧ p1)) ∨ True))) ∧ True)) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765671624374669351391637383162 : (((p4 ∧ ((((p2 ∨ ((p2 → (p4 ∨ (p1 ∧ True))) → False)) ∨ False) ∨ p5) → (p2 ∧ (p3 ∧ (p3 → ((p3 ∧ p1) → (p4 → p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683643508702270556368424284453 : ((((((p5 ∧ ((p2 → (p5 → p3)) ∨ p4)) ∨ (((False → p1) → (p4 ∨ False)) → True)) ∧ p1) ∨ (((p4 → p2) → (p1 → p5)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321037285340549090915219989833 : (p4 ∨ (False ∨ (True → (((p3 → p1) → (((p1 ∨ False) ∧ p2) ∧ p3)) ∨ ((((p5 ∨ p4) → p5) ∧ ((p1 ∨ (True → p4)) ∨ False)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112982566121431449145896044880 : (((p2 ∧ ((p1 → (((p5 → (p5 → (p5 ∨ False))) ∧ False) ∨ False)) ∧ (((p4 ∨ (p4 → p3)) ∧ (p5 ∧ p5)) → False))) → False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178326306296850743764347711401 : ((((p2 → (p3 ∨ (p1 ∧ (p1 ∧ p4)))) ∨ (p3 ∨ p3)) ∨ (p1 ∨ False)) ∨ ((p1 ∨ (p1 ∧ (p1 ∨ ((p4 ∨ True) ∧ p3)))) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68984673162020999817094572856 : ((p5 → ((((p4 → False) ∨ (p1 → (p2 ∨ ((p3 ∧ (p4 → p4)) → (((p1 → p3) → p4) ∨ ((p4 ∧ True) → True)))))) ∧ False) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159010784889658053048808658363 : ((p4 ∨ (((((True → (p5 ∧ ((False ∧ False) → False))) ∨ p4) ∨ (p3 ∨ p5)) → (p1 ∨ p3)) → False)) ∨ (p4 → (p4 ∧ ((p2 ∧ p1) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56169407732622536806477429588 : (((p1 ∧ (False ∧ (p4 ∧ p5))) ∨ (((p2 ∧ p5) → (p2 ∧ ((p1 ∨ p3) ∨ (((False → p3) ∧ True) ∨ ((p1 ∨ False) ∨ False))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159104721204033521775031662450 : ((True → (p1 ∧ (((((p2 → ((True → p5) ∨ p3)) → True) ∨ (p5 → True)) ∨ (p1 ∨ p3)) → False))) ∨ ((p2 ∨ p1) → (p2 → (p5 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769676745880518624845907754061 : (((p5 ∧ (False ∨ (p4 ∨ (((((p2 → (p5 ∨ p5)) ∨ p5) ∧ p4) ∨ ((((p1 ∨ p5) ∧ p1) → (p3 ∨ p1)) → (False ∨ False))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657777687981420840990159918572 : ((((True ∧ ((p4 ∧ p2) ∧ ((((p5 ∨ p4) ∨ p5) ∧ True) → ((False ∧ p4) ∧ (((p1 → True) ∨ (False ∧ p4)) ∨ p3))))) ∨ (p4 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_166867194161499325424729651913 : ((((p3 ∧ ((p3 ∧ True) ∨ (False → (((p4 ∧ p2) ∨ p4) → p4)))) ∧ (p5 ∧ True)) ∧ p1) → ((p1 → ((p4 → p2) → p4)) ∨ (p3 ∧ p3))) := by
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
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160006224656318256726773272895 : (((((p4 → (p5 ∧ p1)) ∨ p5) ∨ ((p1 ∨ p1) ∨ (((p5 ∨ (p5 ∨ p1)) → p3) → p4))) → p4) → (((False ∧ p3) ∨ True) → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40780109436050109105496346824 : ((((p1 ∧ (((p2 → (((((p1 ∧ p3) → p4) → p2) ∧ p4) ∨ p3)) ∧ p2) ∧ (((False → False) ∨ (True → p2)) → p5))) → p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229707628415000611310980685399 : ((p4 → (p1 ∧ p1)) ∨ (p3 ∨ ((((p1 ∨ p2) ∧ (((p1 ∧ p3) → p1) → False)) ∨ (p3 → (p2 ∨ (p4 → (p2 ∨ False))))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_232992933410488584905767357238 : ((p3 ∧ (p4 → p3)) → (((p5 → False) → p4) ∨ ((((((p2 → ((p4 ∨ p1) ∨ p3)) → p1) → p4) → True) ∨ ((p1 → p5) → p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606861598043497374498266693998 : ((((((p1 ∨ (p2 → (p3 ∧ (((False ∨ p3) ∨ (p5 → (p1 ∨ False))) → (True ∧ (False ∧ False)))))) ∨ ((p1 ∨ True) ∨ p3)) ∧ True) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137071463432770217117776385551 : (((p4 → p2) → ((((p4 → ((((p5 ∨ True) ∨ p2) ∧ p2) ∧ p4)) ∨ False) ∧ p3) ∨ (((p1 → p4) ∨ p5) → p2))) ∨ (p5 → (p5 ∧ True))) := by
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
theorem thm_5_vars_638879614605794642074372197267 : ((((((p2 ∨ (p3 ∨ p1)) → p5) ∧ ((False ∨ (p1 → (((False ∨ p3) → True) ∧ ((p3 ∨ p3) → (False → (p3 → p1)))))) → p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774996073728043367067577327744 : (((False ∨ ((p5 ∨ (p1 → p5)) ∨ ((((p4 ∧ p2) ∧ ((((p3 → p1) → (True ∨ p5)) ∧ p2) → False)) ∨ p5) → ((True → False) → p1)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752823967343522588879429849533 : (((False ∧ ((p5 ∨ (p2 ∨ (((True → (p4 ∨ p1)) ∧ ((((p1 ∨ p3) → True) → ((p3 → True) ∨ (p1 ∧ p5))) ∨ p2)) ∧ p5))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185520592074151173825347921313 : ((p3 ∨ (((p5 ∨ p2) ∧ (p5 ∧ ((False ∨ False) → False))) ∨ p5)) ∨ (((p2 ∧ (p3 ∧ False)) ∧ ((p2 → p3) ∨ ((p1 ∧ False) ∨ p4))) → p5)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767442740652522418728215078009 : (((p5 ∧ ((p3 → ((p2 ∨ ((p4 ∧ p2) ∧ (p2 ∧ ((((p3 ∧ p4) ∨ (p1 → (p2 → (p5 → True)))) ∧ p1) → p2)))) ∧ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173896143231668109496437656570 : ((((p4 → (((p4 ∧ False) ∨ (p3 → p1)) ∨ ((True ∨ p5) ∨ p5))) ∨ p3) → p2) → (((((False ∧ p4) ∧ True) → (p1 ∨ False)) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∧ p4) ∧ True) → (p1 ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153354513965262940743387080074 : ((p2 ∨ (((True ∧ ((p5 → p4) ∨ p3)) ∨ p3) ∧ (p4 ∧ ((((p1 → p2) → True) ∧ (p1 ∨ False)) → p5)))) → (((False → p5) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h6.left
        let h12 := h6.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h13
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h6.left
        let h18 := h6.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h19 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h19
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h6.left
      let h24 := h6.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h26
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h25
      -- One of the premise coincides with the conclusion.
      exact h27



