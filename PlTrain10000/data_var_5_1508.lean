variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64128131725870588755872129285 : ((False ∨ (((False ∧ (False ∨ p2)) ∨ p2) ∨ ((p2 ∧ (False ∧ True)) → ((p4 ∨ (p2 → (((p1 ∨ (False → p3)) → p1) ∧ False))) → p3)))) ∨ p4) := by
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_416528076117889805445887289856 : ((((p2 ∧ (p3 ∨ ((True → False) ∧ ((p1 ∨ ((((True ∧ p5) ∨ False) → ((p1 → p5) → p2)) ∨ p2)) → ((p3 ∧ False) → p5))))) → p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175537759265988700433654877873 : ((p4 → ((p4 → p2) → ((p5 ∨ p2) → ((p5 → False) ∨ ((p3 → True) ∨ p5))))) → (((p3 → True) → (p2 ∨ ((p3 ∨ False) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668878484464947514895930949058 : ((((((True → p3) ∧ (((p4 ∧ (p5 → False)) ∧ (((p1 → p1) ∧ p5) ∧ (p4 ∨ (p3 ∧ True)))) ∧ p4)) ∨ False) ∨ ((p1 ∨ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59732791257523334785947602282 : (((p1 ∧ True) → (((((((p3 ∧ p3) ∨ p1) ∨ ((p4 ∧ (p4 → (True ∨ p5))) ∧ p2)) ∨ p1) ∧ (p2 ∧ p4)) ∧ (p3 → p5)) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_307254175453471714360673955403 : (p1 ∨ (p2 ∨ ((((p5 ∨ ((p3 → p1) ∧ p5)) ∧ (True → ((p4 ∧ (p5 ∨ (p1 ∧ p5))) ∨ (False ∧ (p2 ∧ True))))) ∧ p5) → (p2 ∨ p4)))) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h23 := h5 h22
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42162177932483587626321288757 : ((((p3 → p3) → ((((((p5 → p3) → p5) ∧ p3) ∧ True) ∨ p4) ∨ (p3 ∧ ((False ∨ p3) ∨ ((p2 → (False → p3)) ∧ True))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610811192555177440512627710104 : ((((((p4 ∧ (True ∨ ((p4 ∨ False) ∨ ((((p3 ∨ p2) → p4) ∨ p1) ∧ (p2 ∧ p2))))) → (((p2 ∨ p3) → True) ∧ False)) → p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586201464952746286649168731344 : ((((((((p2 ∧ (True → (False → (p1 ∨ p1)))) → p4) → (p1 ∨ p2)) ∨ (((p3 ∧ p4) → p5) ∨ (True ∧ (p4 → p5)))) ∧ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119282119549764648566521243487 : ((p3 → (((((p3 ∨ p4) → ((True ∧ p1) → ((p4 ∧ p5) → ((p2 → ((p1 ∧ True) ∨ p3)) ∨ p2)))) ∨ p1) → p5) ∨ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330435959408614070800704848070 : (True → (p3 ∨ (((True → (p2 → p1)) ∨ ((False → (p2 → (True ∨ False))) → (p4 ∧ (p2 → (p2 → True))))) → ((p2 → p1) ∨ (p1 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (False → (p2 → (True ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h10
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119307697387438662297909552342 : ((p3 → ((p2 ∨ (((p4 ∧ p1) ∧ (p2 ∨ (((p1 ∨ p2) ∧ (False ∧ True)) ∨ p2))) ∧ (False ∧ (p2 ∨ p2)))) ∨ (p4 → p4))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709012717381202002352526650022 : ((((((p3 ∧ p5) ∧ p2) ∧ ((True ∧ p3) ∨ p3)) → (p5 → (((p4 ∨ (p1 → (p1 → p1))) → ((p4 ∧ (p5 ∧ p5)) ∨ p4)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135538424759336148733093966633 : ((((((p2 ∧ (p5 → False)) ∧ p3) ∧ (True → (True ∧ True))) → ((False ∧ p4) ∧ True)) ∧ (p5 ∨ ((p1 ∧ p3) → False))) ∨ (True ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681909738593308583887157420715 : ((((((((p2 ∧ p4) ∨ p4) ∨ ((True ∧ p5) → (((p4 ∧ p1) ∧ p2) → True))) ∧ p3) ∨ p2) ∧ ((p1 → ((p1 ∨ True) ∧ p4)) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40380188859326921191604081972 : (((((p5 ∧ (((p3 ∧ (((p2 ∨ False) → True) ∨ p4)) ∧ p4) ∧ ((p2 ∧ (p4 ∧ (False ∧ p5))) ∨ p2))) ∧ (p1 → p4)) ∨ p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256411223315828252335698763159 : ((False ∨ p3) → (((p5 ∧ p4) ∨ ((((p4 ∨ p3) → (p1 ∧ p2)) ∨ ((((False ∨ p3) ∨ p2) ∧ p2) ∨ p1)) ∨ p4)) ∨ (p2 ∨ (False ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125542765727780573523333950531 : (((False → True) ∧ (p2 ∧ (True ∨ ((((((p1 → (p3 ∧ p1)) ∧ ((p5 ∧ p4) ∧ (p2 ∨ p4))) → True) ∧ p4) → p4) ∧ True)))) → (p3 → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629999868287417082555549620115 : ((((((False → (p2 ∧ (False ∧ p3))) ∨ (p5 → ((p2 ∨ (p1 → p5)) ∧ (((p5 → False) → (p4 ∧ (p2 → True))) ∧ p3)))) ∨ p3) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312157449245722276532533119365 : (p2 ∨ (True → (p1 → (p2 ∨ (p1 → (((((p1 → (p5 → (p2 ∨ p1))) ∧ ((p2 ∧ p5) ∧ p2)) ∨ True) ∧ p5) ∨ ((p2 ∧ p4) → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115147956686934100145447649225 : (((False ∨ ((p3 ∨ (p4 ∨ True)) ∧ ((p3 → True) → (p4 ∧ True)))) → ((p5 ∨ (((p2 ∨ p1) → p2) ∧ p3)) ∧ (p4 ∧ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38191824504668218893697365688 : ((((((((p5 → p1) → p2) → (p4 → ((((p4 ∧ False) ∧ False) ∨ True) ∨ (p5 → True)))) ∨ p2) ∧ True) → ((p1 ∧ p4) ∨ p4)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778436028001111860789554969593 : (((p1 ∨ (p3 ∧ (((p4 → p1) ∨ False) ∨ (p2 ∨ (((p5 → (False → p5)) → p5) → (False ∧ ((((p3 → p4) ∨ p5) ∨ p4) → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736420454736957251916374456751 : ((((p1 → False) ∧ (((((((False → (p5 ∨ p2)) ∧ (p2 ∧ (p1 → p3))) ∨ (((False ∨ p5) ∨ p3) ∨ False)) ∨ p4) ∨ p5) ∨ p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49583817749940705884989510532 : ((((p3 ∨ (p5 ∧ ((((p2 ∧ (p4 ∧ (p4 ∨ p1))) ∨ p5) → p5) ∨ p2))) → ((p3 → (p3 ∨ p1)) ∧ p2)) → ((True ∧ p5) → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (p5 ∧ ((((p2 ∧ (p4 ∧ (p4 ∨ p1))) ∨ p5) → p5) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h5
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716605327260548870946650668379 : (((((False ∧ True) → (p5 → p1)) ∧ (((True ∧ (p4 ∧ p5)) ∧ (p1 ∨ p2)) → (True → ((((p1 ∨ p2) ∧ (False ∧ p4)) ∧ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824607740853003018909523720187 : (((((p3 → (p4 ∧ False)) ∧ (p5 ∧ ((p4 ∨ (p5 ∧ ((p2 ∨ ((p2 ∨ True) ∨ (True ∨ p1))) ∧ (p4 ∨ (p3 → p1))))) → p3))) ∧ True) → p3) ∧ True) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ (p5 ∧ ((p2 ∨ ((p2 ∨ True) ∨ (True ∨ p1))) ∧ (p4 ∨ (p3 → p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h13 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750876069055192589731377741446 : (((True ∧ (((p3 ∧ ((True ∧ p3) ∨ (p5 ∧ p3))) ∧ p4) ∧ ((((False → (((p4 → p4) ∨ (p2 ∧ p2)) → p4)) ∨ p1) ∨ p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783375832107830537141142362716 : (((p3 ∨ (((((p2 → True) ∧ p2) → ((p1 → p3) → p1)) ∨ (p2 → ((p1 ∨ p5) ∧ True))) ∨ (True ∧ (p4 → (p4 ∨ (False → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118415630141875655881285999032 : ((p2 ∨ (p3 ∧ ((p2 → ((p2 → (False → ((((p3 → (False ∧ p5)) ∨ (p4 → (p5 → p2))) ∨ p4) ∨ True))) → p5)) ∧ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310668413959019843064040416652 : (p2 ∨ (((p1 → (True ∧ p2)) → False) → ((p5 → (((p4 → p1) ∧ p1) ∨ (True → ((True → False) → (((p2 → p2) → p3) ∨ p4))))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611734540210367890584554562836 : (((((True → ((((p2 ∧ (p4 ∨ p4)) ∨ (p4 ∨ p2)) → p1) ∨ ((p5 ∨ p3) ∨ (True → (False ∨ ((p5 ∨ p4) ∧ p2)))))) → p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151912452149206214466806299137 : (((False → (((True ∧ (False ∧ (p4 ∨ p2))) ∧ (p4 → p3)) ∨ (p1 ∧ p3))) → (((p4 ∧ p3) ∧ False) ∧ p5)) → ((p3 ∧ (False ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (((True ∧ (False ∧ (p4 ∨ p2))) ∧ (p4 → p3)) ∨ (p1 ∧ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False → (((True ∧ (False ∧ (p4 ∨ p2))) ∧ (p4 → p3)) ∨ (p1 ∧ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227560368179014985811263836026 : ((True ∧ (p4 → p2)) ∨ (False ∨ (((p2 ∧ (p1 → p5)) ∧ ((p5 ∨ (((p3 → (False ∨ p1)) ∧ p4) ∧ p4)) ∨ (p4 ∨ p3))) ∨ (False → p1)))) := by
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
theorem thm_5_vars_217333819813312499078580596297 : (((p1 ∨ (False ∧ p4)) ∨ p2) → ((p2 → (((False ∨ ((((p1 → (True ∧ False)) → p4) ∨ (p2 → p4)) ∨ p4)) ∧ p3) → (p5 ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254634557911789729256129387019 : ((p3 ∧ p2) → (((((((p3 → False) → True) → p2) → p5) ∨ ((((p5 ∨ p5) → (p4 ∧ False)) ∨ (p4 → True)) ∧ p1)) → (p4 ∧ p1)) ∨ p3)) := by
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
theorem thm_5_vars_800397368969115919162703349080 : (((p2 → ((p2 ∧ (((p1 ∧ p4) ∧ (False ∨ ((True → ((p1 ∧ p5) ∨ (p3 → ((p5 ∨ p1) ∨ True)))) → False))) ∨ (False → False))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193064058996578037998484896863 : (((((False ∧ p1) ∧ p3) ∨ p4) ∧ (p2 → (p4 → False))) → (p1 ∨ (p1 → ((((p5 ∨ (p2 ∨ p3)) ∨ p5) ∧ p5) → ((p1 ∧ p2) → False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h11.left
    let h16 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h22 := h20 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h25 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h26 := h3 h25
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h27 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h28 := h26 h27
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h30 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h31 := h3 h30
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h32 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h33 := h31 h32
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h35 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h36 := h3 h35
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h37 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h38 := h36 h37
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192452496233071746620885678077 : ((((((p1 ∧ False) → p4) ∨ True) ∧ (p4 ∨ p5)) ∨ False) → ((p4 → (p3 → False)) ∨ (((((p5 → (True ∨ p4)) ∧ False) ∧ p1) ∧ p5) → True))) := by
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749317670020183175993888677185 : ((((p5 → p5) → (p2 ∨ ((p3 ∧ ((p3 → p3) → (((p5 → (p5 ∨ p4)) ∧ ((p5 → p5) ∧ (True ∧ (False → p1)))) → False))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694580759030507962107424119638 : ((((p3 ∧ ((((False ∧ p5) ∨ (p2 ∧ p3)) ∧ p4) ∧ ((False ∨ p2) ∨ p5))) ∨ ((p4 ∧ (True ∧ (((p5 ∧ p2) → True) → p2))) → p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37753222675331842627261670210 : ((((((p5 ∨ (False ∨ p4)) → p2) ∧ (((((p4 ∨ (False → p5)) ∨ True) → p5) ∧ p1) → (p5 ∨ ((True ∧ p5) → p4)))) → p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50766530553269865151233575481 : (((False ∨ (((((False ∧ False) ∨ p4) ∧ (p5 ∧ ((p5 ∨ (p1 → p4)) → False))) → p2) → (p5 ∨ p3))) → (p1 ∨ ((p2 ∧ p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160639273423672156884071610316 : (((True → ((p2 ∨ ((p3 ∧ (p5 ∨ p2)) → False)) ∨ p4)) ∨ ((p3 → (p4 ∧ True)) ∨ (p3 → p4))) → ((((p2 ∧ p1) ∧ p3) → p5) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112769978924740636192768025346 : (((((p5 → p5) → (((p2 ∨ (p2 → True)) ∨ False) ∨ p1)) → (True ∧ (((False → p2) ∨ p2) ∧ (p4 → (p2 ∧ True))))) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158221325204864294464928652139 : (((p4 ∧ (p2 → False)) ∧ ((p1 ∧ ((p4 ∨ (p1 ∨ True)) ∨ (((p4 → p1) ∨ True) → p2))) ∨ p1)) ∨ (False → (((p3 → True) ∧ False) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114953025416172550328463274610 : (((p1 ∧ (p2 ∧ ((p1 ∨ (False ∧ (p1 ∨ p2))) ∨ ((p1 ∧ True) ∨ p4)))) → (False ∧ (((p4 ∧ p2) ∧ p1) ∧ (False ∨ p5)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134278989381023484694676484612 : ((((p4 → False) ∧ (p2 ∨ (((False ∨ ((False ∧ p3) ∧ ((p5 ∧ p2) ∨ p4))) ∧ ((p4 ∧ p5) ∨ True)) ∧ True))) ∨ True) ∨ ((p4 ∨ p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350930157716588899135140169408 : (p4 → (((((False → p5) ∨ (((p5 ∧ False) ∧ p3) ∨ (p4 ∨ (p3 ∨ p1)))) → (p3 → (p5 ∧ (p4 → (p3 → False))))) → p1) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41213896170509244747504865897 : (((((((p5 ∨ (((False ∧ (p3 → False)) ∧ (p5 → (True ∨ p1))) ∨ p2)) ∨ p1) ∨ p2) ∨ p3) ∧ ((True ∧ p3) → (True ∧ True))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188722071881077364500034459848 : ((((p4 ∨ ((p2 → True) → p5)) → False) → (p1 ∨ True)) ∧ (p1 → ((p2 → p2) → ((((True → (p4 ∧ True)) ∧ (p4 ∨ p3)) ∨ p1) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49193490724782569123685485423 : ((((p4 ∧ (p2 ∨ p4)) ∧ ((p4 → (True → p3)) ∧ (((p2 ∨ ((p4 ∧ (p5 ∧ p3)) → True)) → p5) ∧ False))) ∨ (p3 → (False → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59485046079199182231031414403 : (((p1 → p4) ∨ (((False ∧ p3) ∨ ((False → ((p1 ∧ (p4 ∧ ((p1 ∨ p4) ∧ True))) → (p3 ∧ p5))) → (p4 ∧ (True ∨ p5)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41260065863651359976955923434 : (((((p2 → (p2 → False)) ∧ ((p1 ∧ (True → (p4 ∨ (p5 → ((p2 → p4) → p4))))) → p2)) ∨ (False → (p4 ∨ (p5 ∧ True)))) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54239863144751684121511867399 : ((((((p1 ∨ p5) ∨ p5) ∧ p3) ∧ (False ∨ False)) ∧ ((((p2 ∨ p1) ∨ False) ∨ (False ∧ (p1 ∨ (p4 → p4)))) ∧ ((p4 ∨ True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630802520976844861269771588960 : (((((p5 → (p4 → (False ∧ ((((p4 ∧ p4) → True) ∧ p2) → ((p4 → ((p3 ∧ True) ∨ ((False ∧ p4) → True))) ∨ p3))))) ∨ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741574618620275093186903561394 : ((((p5 ∨ p5) ∨ ((((True → (False ∨ p4)) ∧ (p1 ∨ ((p5 ∧ p2) → False))) → (False ∧ (p3 ∨ ((False ∧ p2) → (True ∨ p1))))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_651973541411560656658532566453 : ((((True ∧ (((p2 ∧ (((((p5 → True) ∨ True) → p4) ∧ (p2 → p2)) ∨ p4)) ∧ p4) ∧ ((p1 ∨ (False ∨ p2)) ∧ True))) ∧ (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198614505230960898631097710304 : ((p2 ∨ (p2 ∧ ((p2 ∨ (p2 ∧ p4)) ∧ False))) ∨ ((((((p4 ∨ ((p5 ∨ p5) → p3)) ∨ (p5 ∨ p5)) → True) ∨ (False → p5)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150051378084032356092039710799 : ((True → (((p5 ∨ (((p5 ∧ p4) → (p4 → ((p4 ∨ (p4 ∧ p2)) ∧ p1))) ∧ p5)) ∧ (p2 ∧ True)) ∨ p3)) ∨ (((p1 → True) ∨ p1) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133654669666940887561688651986 : ((((((True → (p2 → (p5 → (p3 → (((p2 ∧ (p5 → True)) → True) → False))))) ∨ p1) ∨ False) ∨ (False → False)) ∧ p5) ∨ ((False ∨ False) → p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208129809243645639322772567779 : ((((False → p5) ∨ False) → (p5 ∧ p2)) → ((p3 → (((p3 → ((p1 ∧ (True ∨ p5)) → p4)) ∧ p5) → p4)) ∨ ((p5 ∨ True) ∨ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670467710974474642214666788821 : (((((True ∨ False) ∧ (p5 ∨ ((((((p3 ∧ (p1 ∧ p2)) → True) ∧ p1) ∧ (p4 ∧ (True ∨ p2))) → p1) → p3))) ∨ (False → (p3 ∧ p5))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225570983342113393363386758324 : (((False → False) ∧ p4) ∨ (((p3 ∧ p3) ∨ (p2 ∨ (p2 → ((p4 ∨ p2) ∨ (p5 ∨ ((True ∨ False) → ((p3 → p5) → p3))))))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87535865448974308216309923374 : ((((((p1 ∨ True) ∨ True) ∨ True) → False) ∨ (((True → False) ∧ (((False ∧ (False ∨ p5)) ∧ p2) → ((p1 ∨ (p2 ∧ p1)) ∨ p3))) ∧ p2)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p1 ∨ True) ∨ True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699616408407684643049480944043 : ((((((False ∨ ((p1 ∨ p5) ∧ (p4 ∧ False))) ∨ (p2 ∨ True)) → p2) → ((((((p5 → (p4 → p4)) ∧ p2) ∨ p5) ∨ p2) → False) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p1 ∨ p5) ∧ (p4 ∧ False))) ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672779143296384521719504083251 : (((((p2 ∨ (((((((p5 → False) → (False ∨ False)) ∨ False) → p5) → (False ∧ True)) ∧ False) ∨ True)) → (p3 ∧ False)) → (p2 ∧ (False ∨ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((((((p5 → False) → (False ∨ False)) ∨ False) → p5) → (False ∧ True)) ∧ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ (((((((p5 → False) → (False ∨ False)) ∨ False) → p5) → (False ∧ True)) ∧ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146959939355411975548733371716 : ((((p5 ∨ (((p5 ∧ ((p2 → False) ∨ p5)) → True) → ((False ∨ ((p5 ∧ p1) ∧ p2)) ∧ False))) ∨ True) ∧ True) ∨ ((p5 → (True ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238330668925071049687257149588 : ((False ∨ True) ∧ ((p3 ∨ True) ∧ ((False ∧ p5) ∨ ((((p1 ∧ (((p3 → p5) ∧ p2) ∨ True)) → p2) ∨ p4) ∨ ((False → p3) ∧ (p4 → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179151335956753356795642210877 : ((p2 ∧ ((p3 ∨ ((p5 ∨ (((p5 ∧ p2) ∧ p4) ∨ p1)) ∨ True)) ∨ p1)) ∨ (p3 → ((p3 ∨ p1) ∨ (((p2 ∧ (p1 ∧ False)) ∨ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257160135625265166832697244489 : ((p2 ∨ p1) → ((p4 ∨ p3) → ((p5 ∨ ((p1 ∧ p5) → ((p2 → (p1 → True)) ∨ (p4 ∧ p3)))) ∧ (((p2 ∨ (p2 ∨ True)) → p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h27
      -- Implications on the right can always be decomposed.
      intro h28
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h29
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h31 =>
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h32 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h34 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h35 : (p2 ∨ (p2 ∨ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h36 := h29 h35
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h37 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h38 : (p2 ∨ (p2 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h39 := h29 h38
      -- One of the premise coincides with the conclusion.
      exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42645206871258610263712805878 : (((p4 ∨ (((True ∨ ((p2 → (p5 ∨ p5)) ∧ p3)) → (((p3 ∧ (p2 → (True → (False → p4)))) → (p2 ∧ p2)) → p5)) ∧ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49794982727829305328688297097 : (((p5 ∨ (((p5 ∨ (False ∨ ((p3 ∧ False) → p4))) ∧ p1) → ((((p1 → p3) ∧ False) ∨ p2) ∨ (p2 → p5)))) → ((p5 ∨ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258965619870116682578661132804 : ((True → p3) → (((False ∨ (((p3 ∧ ((((p5 ∧ p1) ∨ p4) ∨ p4) → p5)) ∧ p3) ∨ True)) → p1) ∨ ((((p1 ∨ False) ∧ False) ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218962212302487070546937455225 : ((p4 ∧ ((p2 → p2) ∧ p3)) → (((p2 ∧ ((p1 ∧ True) ∧ p4)) ∨ ((p3 ∧ p2) ∨ ((p3 ∧ (p3 ∨ True)) → (p2 ∧ p2)))) ∨ (True → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702646043609042956509983279138 : (((((((p3 ∧ (p2 ∧ True)) → p4) ∨ p3) ∧ (p5 ∨ False)) ∨ (((p4 → ((True → ((p1 ∨ True) → p3)) ∧ p2)) → p5) ∨ (False → p2))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58752973778855919118120055155 : (((p4 → True) ∧ (p3 ∨ ((p3 ∧ ((((False ∧ p2) ∨ p3) → (False ∧ p4)) ∨ ((p1 ∨ p5) ∧ p4))) ∨ (p1 ∨ ((p5 ∨ p4) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748896080777409862545866683793 : ((((p4 → p2) → ((((p3 → ((p2 → p3) ∧ p2)) → p3) ∨ (((True → False) → ((True ∨ (p2 ∧ p1)) ∨ (p1 → p1))) ∨ p2)) ∨ p2)) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135503653713576131338990619701 : (((p1 ∨ ((p4 ∨ p1) ∧ ((False ∧ (((p3 ∧ (p2 ∧ p4)) ∨ p4) ∨ (False ∧ True))) → p5))) → ((p4 ∧ False) ∧ p3)) ∨ (p1 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789846804471531897687393029436 : (((p5 ∨ (((p1 ∧ p1) ∨ p4) ∨ (((p3 ∨ (True ∧ p2)) ∨ (True ∨ (((((p3 ∨ p4) → p1) ∧ (True → p5)) → p4) ∧ p2))) ∧ True))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114653907227722832257222285485 : ((((((((p2 → p4) → False) → True) → p2) ∨ p5) → ((False ∨ p4) ∧ (p4 → p2))) ∨ (False → (p3 ∨ ((False ∧ False) ∨ p4)))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112659443426359807903125723595 : (((((p5 ∨ (p5 → ((p2 → ((False ∧ True) ∧ p4)) → ((p2 → (p2 ∨ p3)) ∨ p2)))) ∧ p3) ∨ (p4 → (True → p5))) → p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178605019899105022156627550668 : (((p2 ∧ ((p1 ∧ (True → p4)) → False)) ∨ (p1 ∨ (p1 ∧ (p3 ∨ p5)))) ∨ (False ∨ ((True ∧ p4) → (True → (p4 ∧ (True ∨ (p3 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342991031670401201192269595066 : (p2 → (((True ∨ True) → (False ∧ p4)) ∨ (((p5 ∨ ((False ∨ p3) ∧ p2)) ∨ (False ∨ (True ∨ ((True ∧ p2) ∧ (p3 ∧ (p5 → p1)))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_209279125147030705683580874308 : ((True → ((p5 ∧ (False ∧ p4)) ∨ False)) → (False ∧ ((((p4 ∨ p3) ∨ (p5 ∧ p5)) ∨ p3) ∧ (True ∧ (((True ∧ (p5 ∨ p2)) → p4) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- False on the left can always be used.
      apply False.elim h27
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h32 := h1 h31
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- False on the left can always be used.
      apply False.elim h36
    case inr h38 =>
      -- False on the left can always be used.
      apply False.elim h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322540708959669719621899527164 : (p5 ∨ ((p5 ∧ ((p2 → (p3 → True)) → (((False ∧ (p4 → (((p1 ∧ (p4 ∨ p3)) ∨ p2) ∨ p4))) → (p5 ∧ False)) ∧ (False ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320473794557207743502590924078 : (p4 ∨ ((p2 → True) → (((p3 ∨ ((p1 ∨ (p2 ∧ p5)) ∨ (p3 → (False → (False ∧ False))))) → p3) → (p4 → (p3 ∨ ((p5 ∨ p2) ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ ((p1 ∨ (p2 ∧ p5)) ∨ (p3 → (False → (False ∧ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228585421302475289916509656172 : ((p1 ∨ (p4 ∨ p4)) ∨ (p3 ∨ (p2 → ((p1 ∨ (p5 → p2)) ∨ (p1 ∨ (((True ∧ (((p2 → p3) ∨ p4) → p3)) ∨ p2) ∧ (p5 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47392677241975054728085836919 : ((((p3 → p4) → (p3 ∧ (p4 ∧ (((False ∨ (((p5 → p3) ∨ (p3 ∨ False)) ∨ p1)) ∧ ((p3 ∨ True) → p5)) ∧ p3)))) ∨ (False → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22203878014354562304459182635 : (((p5 ∧ (((p2 → p4) ∧ (p2 → True)) → p2)) ∨ (((p4 ∨ ((False ∧ p2) ∨ p4)) ∧ (p1 ∧ (((p5 ∧ p5) ∧ p5) → p2))) → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356402073768721538320922733756 : (p5 → ((((p3 ∧ p3) ∨ (False ∨ ((p1 ∨ (p5 ∨ p1)) ∨ False))) ∧ p5) ∧ (p4 ∨ ((p4 ∨ ((((p4 ∧ True) ∨ p3) ∨ p1) → True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117936841991379279293026465005 : ((p5 ∧ ((p5 → p5) → ((p5 ∨ True) ∧ ((p5 ∨ (p3 → p1)) ∨ (((True ∨ (False ∨ (p5 ∨ False))) → True) ∧ (p5 → p4)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60242581880345458726313495370 : (((True → p5) → (p3 ∧ ((p5 ∧ (p2 ∧ (False ∨ ((True ∧ p3) ∧ p5)))) ∨ ((p5 ∧ p2) → ((((p1 ∨ False) → False) ∨ False) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118141665540014896075250961495 : ((False ∨ ((p1 → ((False ∨ p5) ∧ ((((p5 → p1) ∧ (p1 → p5)) ∧ p1) → False))) ∨ (((p3 ∨ True) ∧ (p2 → p1)) ∨ True))) ∨ (p5 → p5)) := by
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
theorem thm_5_vars_787671812922157487149419507795 : (((p4 ∨ (p4 ∨ ((p2 ∨ ((((p3 ∧ p5) ∧ (p3 ∧ p5)) ∧ (True → (p2 ∨ p4))) ∧ p3)) ∨ ((False ∨ p2) → (False → (p2 ∧ True)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185213452491646117446130971034 : ((True ∧ (p1 → (((True → False) ∧ (p3 → True)) ∨ (p4 ∨ False)))) ∨ (p5 ∨ ((((p2 ∨ (p2 ∨ (p1 → p4))) ∨ p5) ∨ (p1 ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114378719377838859597126214430 : (((((False → ((p2 ∧ p3) → p1)) ∧ ((p1 ∧ p1) ∨ (p4 ∧ ((p2 ∨ True) ∧ False)))) → False) ∨ (p1 → ((p5 → True) ∨ p5))) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_43592099872707174756526403845 : ((((((p2 ∧ p5) → ((p4 ∨ p3) → ((((False ∨ p2) ∨ True) → (p5 → p1)) → (((p2 ∧ p2) ∨ True) → False)))) ∨ p2) → p2) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354885157285880717609556805957 : (p5 → ((p2 ∧ ((p3 ∨ (False ∨ p5)) → ((p3 ∨ (p1 ∧ p5)) ∧ ((p1 → (True → ((p2 ∨ ((p1 ∧ True) ∧ p1)) → p5))) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112076547811107422565968716154 : ((((p1 ∧ p2) ∨ (((p4 ∨ ((p3 ∨ True) → p1)) → ((p3 ∧ p3) → ((True ∧ (p5 → False)) ∨ (p3 ∨ p1)))) → p2)) ∨ p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



