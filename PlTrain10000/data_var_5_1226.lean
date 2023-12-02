variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208586112737834909955938935042 : (((p1 → p1) → (p3 ∨ (True → False))) → (((((((p3 ∨ True) ∨ ((p3 ∧ p1) ∧ p1)) → p4) ∧ True) → (p2 → p5)) ∨ True) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38337323991359362391396932510 : (((((((p3 ∨ (p1 ∨ (False → p1))) ∧ ((p2 ∧ p1) ∧ p4)) → p5) → (p1 → p2)) ∧ ((((p2 ∧ True) ∧ p2) ∧ False) ∨ p4)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644291353811977490231879922705 : ((((False ∨ ((p5 ∧ ((p3 ∧ (((p2 ∧ ((False ∧ (p1 ∧ (p1 ∧ p2))) ∧ p5)) ∨ p5) → p1)) ∧ (p2 ∨ p4))) → (p1 ∧ p2))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47412020021513644094699736726 : (((False ∧ (((p1 → (True ∧ p3)) ∨ (False ∧ True)) → (((p4 ∨ (p1 ∧ p4)) ∧ True) → (p4 → ((True ∨ p3) → False))))) ∨ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49634627967963041596558938693 : ((((p2 ∧ (p2 → ((p2 ∧ p2) → False))) → (p4 → (((True → (p1 ∨ (p4 ∧ p5))) ∨ (False ∨ p2)) ∧ p5))) → (False ∨ (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147598703465727843316595045140 : (((((p4 ∧ ((((p1 ∨ p5) ∧ p4) → (p2 ∨ (p3 ∨ False))) ∧ p2)) ∨ ((False → p5) → p1)) ∨ p4) → p1) ∨ (((True ∨ p4) ∧ p2) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158016035997529297998036996950 : ((((p4 ∨ (p5 → (p5 ∧ False))) → p2) ∧ ((((p1 ∨ False) ∨ (p3 ∧ (True ∨ p1))) ∧ False) ∨ p3)) ∨ ((((p5 ∨ p3) ∧ p2) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681278379971535577819094603915 : ((((p5 ∧ (True ∧ (False ∨ (((p4 → p2) → p1) ∧ ((((True ∧ True) ∨ (True ∧ p5)) ∧ p5) ∧ p5))))) → (p4 ∧ ((p1 ∨ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231837369807793048393582475127 : (((p5 ∧ p2) → False) → (((((p5 ∧ (p1 ∨ ((p5 → p1) ∨ (((p4 ∨ p4) → p1) → (p3 ∧ p3))))) ∨ (p3 ∧ p1)) ∧ p4) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40390574982319768805548627252 : (((((((((p3 ∧ (p4 ∨ (True → p5))) → (p2 ∨ p1)) → p3) ∧ (True ∨ (p2 ∧ (p3 → p2)))) → False) → (p2 → p4)) ∨ True) ∨ p3) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186834447643034301517503255318 : ((((p4 ∨ (p1 ∨ p4)) → p1) ∨ (((p1 ∧ p2) ∧ p3) ∨ True)) → (p3 → (((p2 → (p3 ∧ (p1 ∧ False))) ∧ p5) → (p2 → (p4 ∨ p4))))) := by
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
  cases h1
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h24 := h5 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764565703785820145267827347936 : (((p4 ∧ ((((p2 ∧ ((((p3 ∨ p1) ∧ p4) → True) ∧ True)) ∧ (((False ∧ p2) ∧ (p3 → False)) ∨ (True ∨ True))) ∨ (True ∧ p3)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_474039389508535442471824585305 : ((((True → (p4 ∧ (((((False ∨ p4) → p1) → p3) ∧ p1) → p1))) → (p1 ∨ ((p1 ∧ (((p3 ∨ False) ∧ p2) ∨ p4)) → (p4 ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698657880681763679042378298671 : ((((((p1 → p4) ∧ p1) → ((p3 ∧ p5) ∨ ((p3 ∨ p5) ∨ p5))) ∨ ((((True ∨ p3) → True) → (False → (p3 → True))) → (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263883955314702639211759465467 : (True ∧ ((((p2 ∧ (True ∨ p1)) ∨ (((p2 ∧ False) ∧ p4) ∨ (p5 ∨ True))) ∨ False) ∨ ((p3 → ((p5 → p4) ∨ p3)) → ((True → p4) ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217796867875456661068042581760 : (((p1 ∨ (p1 ∧ True)) → p2) → (((p2 ∧ True) ∨ (p3 → (((p4 → p5) ∧ (p3 → p1)) ∨ True))) ∨ ((p3 ∧ ((False ∧ p1) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647066842806177840826918063856 : ((((p3 → (((True ∨ ((p4 ∧ p3) → (((True ∨ (True ∨ p3)) → (False → p3)) ∧ False))) ∧ p4) → ((p3 ∨ (False → False)) → p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684674058039705868385953489466 : ((((((True ∧ p2) ∨ p1) → (p4 → ((p1 ∧ ((((True → False) ∨ p3) → p3) ∧ p3)) ∨ p4))) ∨ ((p4 → p1) → ((p4 → p3) → p5))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607006528951501345399338449501 : ((((((p5 ∧ ((((True ∧ ((False ∧ p2) ∨ (p4 ∨ False))) ∧ p4) → p4) → p4)) → ((p1 ∨ (p4 ∨ p3)) ∧ (False → p2))) ∧ False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594011226377430895461372259651 : (((((p2 ∨ (((p2 → p2) → (p5 ∨ (p5 ∨ (p2 ∧ (p3 ∨ p3))))) ∨ ((True → p3) ∨ True))) ∨ (p4 ∧ ((p4 ∧ p4) ∨ p5))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355588787680004037204486866727 : (p5 → (((((p4 ∧ True) ∨ p3) ∨ (p4 ∨ (p5 → p5))) → (((p5 ∧ ((p4 ∧ p2) ∧ (False ∧ p3))) ∧ p4) ∨ (p3 → p5))) ∨ (p4 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200747987528414241810910395846 : ((p3 ∧ (True ∨ (p4 ∨ (True ∨ (p4 ∧ p5))))) → (((False ∨ (((p1 ∧ p1) ∨ (p2 → (False ∨ (p3 ∧ p2)))) → (False ∧ p4))) ∨ p3) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56911236030157859436719604958 : (((p5 ∧ (p3 ∧ True)) ∧ ((p2 → True) → (((False ∨ p3) ∧ (((p1 → (p1 ∨ p4)) → (p1 ∨ (p1 → p5))) ∧ (p1 ∨ p5))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234857952158526344127861550607 : ((p5 → (False → p1)) → (((((p4 ∨ p1) → (p5 ∨ (((p2 ∨ (p3 ∧ (p1 ∨ p2))) ∨ True) → (p1 → p4)))) ∨ p4) ∧ p4) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345396583822363608245274779688 : (p3 → (((((p5 ∨ p1) → ((p1 ∨ ((p4 ∨ p3) → p1)) → (p3 ∧ ((((p4 → (p2 → p1)) ∨ p3) ∨ True) → False)))) ∨ p4) → p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206560230067686637431300262907 : ((True → (p3 ∨ (p4 ∨ (p4 ∨ p2)))) ∨ ((p4 → False) ∨ ((p2 → (((p5 ∧ p4) → (((True ∧ p4) ∧ p2) ∨ p4)) ∨ (p4 ∨ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147943875226919066249283636118 : ((((p5 ∧ False) ∨ (p3 ∧ ((p1 ∨ (p2 ∨ (((p4 ∧ False) → p4) → (True ∨ p2)))) → p3))) ∧ (p3 ∨ p4)) ∨ (p4 → ((p4 ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191777256009958404019226480684 : ((p1 ∨ ((p2 → p1) ∧ (((p3 ∨ p2) ∧ p1) ∧ p2))) ∨ ((p2 → (p4 ∨ p1)) ∨ (True → ((p5 ∨ (p1 ∨ (p4 ∨ (True ∧ False)))) ∨ True)))) := by
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
theorem thm_5_vars_335697176814632606044807949005 : (p1 → (((((False ∧ p2) ∨ (p3 ∧ (p3 ∧ (((p5 → p2) → p2) → (True ∨ False))))) ∧ ((p5 ∧ True) ∧ (p1 ∨ (p3 → p1)))) ∨ p1) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350104957739077923468967426182 : (p4 → ((((((((p5 ∧ (p2 ∧ p2)) → p3) ∨ (True ∧ (p5 ∨ False))) ∨ (p3 ∨ False)) ∨ p5) ∨ p3) ∧ (p5 → (True ∧ (p1 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800193948661820527021017341825 : (((p2 → ((((p3 → (((p1 ∨ p5) → (True → ((p2 ∨ (p5 ∨ p4)) ∨ True))) → (((False → p3) ∧ True) ∨ p4))) → False) ∧ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3447135011509639410953569045 : (True ∧ ((p2 ∧ (False ∧ p3)) ∨ (p3 ∨ (True ∧ (((p4 → p5) ∧ (p2 ∨ p1)) → ((p2 ∧ p1) ∨ ((p4 ∨ (p4 ∧ p3)) ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659677269980116365183614615676 : (((((((p2 ∨ p4) ∨ p3) ∨ ((((True → True) ∧ (False → (p4 ∧ False))) ∨ ((p3 → p1) → (p1 ∧ p5))) ∨ p3)) ∧ p5) → (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179334600205490627102500955914 : ((p1 ∨ ((((p4 ∨ (p4 ∨ False)) ∧ p3) → True) → (p5 → (p1 ∧ p5)))) ∨ ((p4 ∧ (p1 ∧ (p1 → (((False ∨ p2) → p3) → False)))) → p1)) := by
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
theorem thm_5_vars_133653727374104237465209819075 : (((((((p3 ∧ ((True ∧ (p4 → p4)) → (p3 ∨ p3))) ∨ p1) ∨ (p3 ∧ (p1 ∧ p5))) ∧ True) ∨ (p3 ∨ p2)) ∧ p3) ∨ (p2 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46985579449273269572115890513 : (((((p4 ∨ ((False ∧ (p2 ∨ p3)) ∨ (p2 ∧ (p2 → (p3 ∨ (p1 ∨ (p5 → False))))))) → (True ∨ (p3 ∧ p2))) → p5) ∨ (p1 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58642124489076089375789905389 : (((p1 → p1) ∧ (((p4 ∨ p2) → (((p3 ∧ p4) ∨ (True ∧ ((p5 ∨ (p4 ∧ (True → False))) → p2))) ∨ ((p5 ∧ p1) ∨ True))) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157557244313249901756312328956 : (((((p4 → (p5 ∨ ((True ∨ (False ∧ p2)) ∧ False))) → p4) ∧ ((p1 → p4) → True)) → (p3 ∧ False)) ∨ (True ∨ ((p3 ∨ p1) ∨ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152247618728966927687503463069 : ((((p5 ∨ (p5 ∨ p1)) ∧ (p1 ∨ p1)) ∨ (((((p5 → p3) ∨ p4) → p4) ∨ ((False → False) ∧ p5)) ∧ False)) → (p5 → ((p2 ∨ p1) ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116161193036855926762120556971 : (((p4 ∨ (p4 ∨ p4)) ∧ ((p3 → (((((True ∧ ((p5 ∧ p5) ∧ p1)) ∨ (p5 ∧ p3)) ∨ (True ∨ False)) → p3) ∧ False)) ∨ p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319479313516723654858419977223 : (p4 ∨ ((((p4 ∧ p2) → (((p1 ∧ False) ∧ (p3 ∧ p4)) ∧ p4)) ∨ p1) → ((((p4 ∧ (False ∧ (p5 → p5))) ∨ (p3 ∨ False)) ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63050528633575308820938430179 : ((p5 ∧ ((((True ∨ ((p1 ∨ p5) ∨ ((p2 → p2) ∧ p5))) ∨ p1) → ((p3 → (False ∧ (p3 → p1))) → ((False ∧ p1) ∧ p3))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157891747316527962678653390062 : (((p5 ∨ ((((False → p5) ∧ p4) ∧ p4) → (p1 ∨ p3))) ∨ ((p1 → p2) → ((False → p4) ∨ p1))) ∨ ((((p4 → p5) ∨ False) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135484765531553616136760296595 : ((((p4 → (True ∨ p2)) ∧ ((p3 ∨ ((p2 ∧ ((p3 ∨ (p3 ∧ p4)) ∨ p3)) ∨ p4)) → p5)) → ((p2 ∨ p1) → p4)) ∨ ((p1 ∧ p2) → p1)) := by
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
theorem thm_5_vars_165890374362220995394197394342 : ((((p4 ∨ p1) → p1) → (p5 ∧ ((((False ∧ (True → (p2 → True))) ∧ p4) → p1) → p1))) ∨ (p4 ∨ (((p1 → p2) → True) → (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302751619990405385907643503401 : (False ∨ (p4 ∨ ((((p2 ∧ (False → (p5 → (p1 ∨ (p4 ∧ p5))))) ∨ (p3 ∨ (p4 → p2))) → ((p5 ∨ (False ∧ p2)) → p2)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_119391926915785224603018657184 : ((p4 → (((p1 ∨ (p1 → (p5 ∧ (True ∨ (((p2 ∧ False) → p5) ∧ p4))))) ∧ (((True ∨ False) → (p2 ∧ False)) ∨ p3)) ∧ p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165475133950794221280287909962 : (((((p4 ∨ (p2 → (False ∧ p5))) ∨ (False ∨ p5)) ∧ False) ∨ (False ∨ ((False ∧ p5) ∧ p2))) ∨ ((False ∧ p5) → (((True → p1) → p2) → p4))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166660840580016477768618315552 : ((p1 → (p2 ∨ (p2 ∨ (((True ∨ p5) ∨ p1) → (((p5 ∨ True) → (p5 → p2)) ∨ True))))) ∨ (((p5 → p1) ∨ ((p5 ∧ p5) → True)) → p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44523808481126028487167746991 : ((((p1 ∨ (p5 → ((p2 → ((p4 ∧ p1) ∧ p5)) ∧ p2))) ∨ (((((p5 ∧ p2) ∧ ((True ∨ False) → p5)) ∨ p4) ∧ False) → p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113455081879215585254759054429 : ((((((((p4 → p4) ∨ ((p2 ∨ (p5 → p2)) → (((False ∨ p2) ∨ p3) ∧ p5))) ∨ p3) ∨ p4) → p1) → p3) ∨ (p2 → True)) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301275228996733208465617208021 : (False ∨ ((((p5 ∨ (p1 → True)) → False) ∧ p4) → ((((p5 ∨ p5) → False) ∨ False) ∧ (((p4 ∧ p3) → (False ∧ p1)) ∨ (True ∧ (p5 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_148257804540990275456351904479 : (((p3 ∧ (((((p2 ∧ ((True ∧ (p4 ∨ p3)) → p5)) ∧ True) ∨ p1) → p4) → p3)) ∨ ((True → p5) ∨ p3)) ∨ ((p4 ∨ (p2 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65658581195742439847746892303 : ((p4 ∨ ((p3 → (((((True ∧ (((True → (p5 ∧ (p4 ∨ p3))) ∧ (p4 ∨ p1)) ∧ p5)) → p4) ∧ False) ∨ p3) ∧ (True → p3))) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788144816429731613170233218996 : (((p5 ∨ (((p3 → ((((p5 → True) → p1) → True) ∧ (p1 ∨ p1))) ∧ ((p5 → ((p1 → p3) → (True → (p2 ∨ p4)))) ∨ True)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91394641158499619468622527654 : (((p4 ∧ False) ∨ (True ∧ (((p2 ∧ ((p3 ∧ p1) ∨ p2)) ∨ (True → p4)) ∧ (((((False → p2) → p1) ∧ p4) ∨ True) → (False ∧ p4))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h17 : ((((False → p2) → p1) ∧ p4) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h18 := h9 h17
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h21 : ((((False → p2) → p1) ∧ p4) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h22 := h9 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192970694240891365007316979053 : (((p4 ∨ (p4 → (p1 ∨ (p1 ∨ p3)))) ∨ (False → p2)) → (((False ∧ p3) ∨ ((True → (((p3 ∧ p5) → True) → p1)) ∨ p1)) ∨ (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259253339247851344713545796897 : ((False → p1) → ((p1 → (((False ∧ p3) ∨ (((True ∧ p4) ∨ (True ∧ p5)) ∧ ((True ∧ p1) ∧ (p1 ∨ (p4 → p4))))) → (p3 ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1785980249653584616151964917 : ((((((((p3 → p1) ∧ p3) → (False ∧ p2)) ∨ (p1 ∧ p4)) → True) ∨ p2) → (p2 ∨ (p1 ∨ (p1 ∨ True)))) ∨ (p5 ∧ (True ∧ p3))) := by
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
theorem thm_5_vars_697202733838017106606113673277 : ((((((p5 ∨ True) → False) ∨ (((p1 ∨ p5) ∨ p5) ∨ (False → True))) ∧ ((False ∧ (True ∨ p2)) ∧ (((True ∧ p3) ∨ (True ∧ p2)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344496632982969908596511146109 : (p2 → (True → (((p3 ∨ (True → False)) ∧ p1) ∨ ((p1 ∨ (((False → ((p3 ∨ False) ∧ (False ∧ p2))) → p4) → False)) ∨ (p4 → (False → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717732020501817250575234130913 : ((((((p5 ∧ p2) ∨ p2) ∧ p2) ∨ (((((True → (p4 ∨ (p1 → (p4 → p1)))) ∨ p5) ∧ ((p1 ∨ p4) ∧ p4)) ∧ p2) ∨ (True ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113584295179109748157163941019 : (((p2 ∧ (((p2 → p4) ∧ p4) ∧ (p3 ∧ ((((p3 → (p5 → p4)) → False) ∨ p4) ∧ ((p3 ∧ p2) → p2))))) ∨ (True ∧ True)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_552448610725428086602248423 : ((((p2 ∧ p2) ∨ (((p5 ∧ (((p4 → (p3 → p1)) ∧ False) → ((p3 ∧ False) ∨ (p2 ∧ True)))) → (p2 → p1)) → p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631655824391605557222554787863 : ((((((((False ∨ p5) ∧ p2) ∨ (((p1 ∧ ((True ∧ p3) → p1)) ∨ p2) ∨ p1)) ∧ (p5 → ((p4 ∧ False) ∧ (p5 → p4)))) → p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610305077103866803564064031978 : ((((((p1 ∨ ((p2 ∨ (p5 ∧ p4)) ∧ ((((p3 ∨ (p5 ∨ p3)) → True) → p4) → (p3 ∧ ((p4 → True) → p3))))) ∨ p1) → p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260470326782642266748765893671 : ((p3 → False) → (((((p2 ∧ p5) ∨ (False → ((p3 → ((p4 ∧ (p2 → p2)) → p5)) → False))) ∧ (p1 → p3)) ∧ (p1 ∧ (p1 ∨ p3))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h25 := h6 h24
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h29 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h30 := h1 h29
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40870586703849356940536291911 : ((((((((p3 ∨ (p3 ∨ False)) → p5) ∨ (((False ∧ (False → p5)) ∨ (p4 ∧ p1)) ∨ True)) → False) ∧ (p4 ∧ p5)) ∧ (False ∧ p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673608258754449534576520262628 : (((((p4 ∧ (p2 ∧ p2)) ∨ ((p1 ∧ p1) ∧ ((p2 ∨ p2) ∧ ((p3 → (True → False)) → (True → (p4 → False)))))) → (p2 ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699900609684343686278451217636 : (((((p2 ∧ (((p3 ∧ True) ∨ p2) ∨ p5)) ∨ (p1 ∨ (p2 ∨ p5))) → ((p3 ∧ ((((p4 → p4) → (p5 ∨ p5)) ∧ p2) → p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299436147062723664700776007932 : (False ∨ ((False ∨ (((p1 → (p2 ∧ (p2 ∧ p2))) ∨ p5) ∧ (p5 ∧ (p4 ∧ ((p3 ∧ p3) ∧ ((p5 → False) ∧ (p1 → (p5 → True)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221979290583683428618802611170 : (((False ∨ True) → True) ∧ ((p4 ∧ ((((((p5 → False) ∧ p3) ∨ p5) → (p3 → (False ∨ p1))) → ((p4 → (True ∧ p2)) → p4)) ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139111202180275257864013202998 : (((((p4 ∨ ((p2 ∨ p3) ∨ ((p4 ∨ p2) → p2))) ∨ (((p4 → False) ∧ p4) ∨ p5)) ∨ (False → (False → True))) ∨ False) → ((p4 ∨ True) ∨ p2)) := by
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h8 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h8
            case inr h9 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712002689232148002977891609790 : (((((((False → p4) → p4) → p5) ∨ p4) ∨ ((p5 ∧ (((True ∧ (True ∨ ((p3 ∨ ((p2 → p3) ∨ p2)) ∨ p2))) ∨ p3) ∨ False)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227003161510520774197853000585 : (((p1 ∨ p3) → p2) ∨ ((p5 → ((False → False) → (p2 → ((True → False) → (((False ∧ p1) → (p5 → p3)) → ((p3 ∧ p3) ∨ p1)))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225111598404351343095478281246 : (((p2 ∧ p3) ∧ True) ∨ ((p2 ∨ (((False → (((p2 ∨ (False ∨ False)) → p1) ∨ p1)) ∧ p4) → False)) ∨ (False → (p1 ∧ ((p5 ∨ p5) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195693141511762844835030493340 : (((p3 ∧ p2) ∨ ((p3 ∧ p1) ∨ (p4 → True))) ∧ ((p3 ∨ (p1 → (((True ∧ (p2 ∧ p5)) ∨ False) ∨ True))) ∨ ((True → (True ∨ p5)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213301911217924170080466950249 : (((True ∧ (p4 ∧ p1)) ∧ p3) ∨ (False ∨ (((p1 → ((p3 ∨ (p5 → (p2 ∨ (p1 → (p1 ∧ p5))))) ∨ p3)) ∨ p5) ∨ ((p5 ∧ p1) ∧ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58826590849478309842937627697 : (((p5 → p5) ∧ (p3 → (((p5 → (((False ∨ (p4 ∧ p3)) → True) → ((True → False) ∧ (p1 ∧ p1)))) → (p3 ∧ False)) ∨ (p2 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748625351425144113104539449815 : ((((p3 → p2) → ((p1 ∨ ((False ∨ p1) ∧ (p3 ∧ ((p3 ∨ ((p5 → p2) ∨ ((p5 ∨ (p2 ∧ p5)) ∨ p1))) → (p3 → p1))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173792649148275228024000296405 : (((True ∧ ((((((True ∨ p3) ∧ p5) → p5) → p5) → False) ∨ (p4 → p2))) ∨ False) → (((((True → p2) ∨ p1) ∧ False) ∨ True) ∨ (p2 → p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350226685063633010017395716853 : (p4 → (((p5 ∨ p2) ∨ ((((p5 → False) ∧ ((p3 ∨ ((p4 ∨ p2) → (p4 ∨ ((p4 ∨ p2) → p1)))) ∨ p1)) → False) ∨ (p3 ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197642378069130359458033365371 : (((((True ∨ p2) ∧ p4) → False) → (True → False)) ∨ (((p5 ∨ p3) ∨ True) ∧ ((p5 → (p2 ∧ ((p5 ∨ p1) ∧ p2))) ∨ ((p3 ∧ False) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242154423615287314126009331515 : ((p2 → True) ∧ (((True → True) → p4) ∨ (((p4 ∧ ((p4 ∨ (p1 ∨ p4)) ∧ (((p1 ∨ (False → p1)) → p5) ∨ p5))) → (p4 ∧ p4)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919262155764361191580248691527 : ((((((p3 ∨ (True ∨ False)) → False) ∧ ((p1 → (p4 ∧ (p2 → True))) ∨ p5)) ∧ (p5 ∨ ((p1 ∧ p4) ∧ (True ∧ (p1 → (p4 → p2)))))) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h12.left
      let h16 := h12.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h25.left
      let h29 := h25.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h30 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h31 := h4 h30
      -- False on the left can always be used.
      apply False.elim h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116110259941224627449884786210 : ((((p1 ∨ p4) → p1) ∧ ((((((p2 ∨ False) → p5) ∧ (p5 → p1)) → ((p2 ∧ True) → p4)) ∧ p4) ∨ ((p4 ∨ True) → p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84712000446804201627951791793 : ((((False → (((p5 ∧ p3) → p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p1))) → p5) ∧ ((p1 ∨ ((p5 ∨ p5) → p5)) ∨ ((p5 ∨ p1) ∨ p1))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (False → (((p5 ∧ p3) → p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (False → (((p5 ∧ p3) → p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (False → (((p5 ∧ p3) → p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p1))) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (False → (((p5 ∧ p3) → p2) ∨ ((p1 → (p3 ∧ p2)) ∧ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55563257367684850118829126199 : (((p4 ∧ (p1 → (p4 ∧ (p4 ∨ p5)))) → ((((p1 ∨ (((True ∧ p2) ∨ (p3 ∨ p1)) → (p5 ∨ p5))) → (p3 → False)) → p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695332394597708428164733644410 : (((((p2 ∧ (((p3 ∧ (p5 ∨ (True ∨ p2))) ∨ False) → (False → p2))) → False) → ((p3 ∧ p2) ∧ (p1 ∧ ((p2 → (p1 ∧ p3)) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693066758553421410270872954684 : ((((p1 ∧ (((False ∧ ((False → p5) ∨ p3)) ∨ (p1 → False)) ∧ (p1 ∧ p2))) ∧ ((p5 ∧ p4) ∨ (((p4 ∧ p2) ∨ p5) ∨ (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314444970042026852952971295251 : (p3 ∨ ((p3 → ((True ∨ (p4 → (p1 ∨ (p4 → p3)))) ∧ ((((False → p1) ∧ p5) ∨ p5) ∨ (False ∧ p4)))) ∨ (False → (p1 ∧ (True ∨ p2))))) := by
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
theorem thm_5_vars_801445229902561610053011691325 : (((p2 → (((p3 ∨ ((p3 ∨ (p4 ∨ p3)) ∧ (p4 ∨ p3))) ∨ True) → ((((p2 ∧ (p1 → p4)) ∧ p4) ∨ ((p5 ∨ p3) ∧ True)) ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
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
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620167003030820235831346955470 : (((((p2 ∧ p1) ∨ (p5 ∨ (((((p4 ∧ True) → (True ∧ True)) → p4) ∨ ((((p5 → p5) ∧ p1) ∧ p5) ∨ (False → False))) ∨ p4))) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_701909477228280228025418986273 : ((((p1 ∨ ((True ∨ ((p5 → p2) ∨ (True ∨ p2))) → p4)) ∧ ((((p4 ∧ p3) ∨ ((p2 ∧ (p2 ∧ p5)) ∨ p5)) → p1) ∧ (p3 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215152218199207716030318545555 : ((True ∧ ((p1 ∧ p5) ∧ p3)) ∨ (True → (p4 → ((((((p2 → p3) → (p3 ∨ ((p2 ∨ True) ∨ p2))) ∧ p5) ∨ p3) ∧ p5) ∨ (p4 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_249119339346173559052278103325 : ((p4 ∨ p2) ∨ (((((((True → p2) ∧ (p4 → p3)) ∨ ((p1 → p4) → (False ∨ (p2 ∨ (True ∨ p4))))) ∧ p2) ∨ p3) → p5) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318868202767543729236200634986 : (p4 ∨ (((((p5 ∨ False) → (False ∧ (((p2 ∧ (False ∨ False)) ∧ p1) → (p4 ∧ False)))) → False) ∧ (p2 ∧ (False → p5))) ∨ (p2 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_248850693223725866553062767962 : ((p3 ∨ p4) ∨ (p4 ∨ (((p1 → (((False → p5) ∧ p5) ∨ p5)) → ((p5 → ((p5 ∨ p3) ∨ (p1 ∧ (p2 ∨ p1)))) ∧ True)) ∨ (p4 ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16868326661163469722900710572 : ((((p3 ∨ False) ∨ ((((((True ∨ (p1 ∧ p2)) → (p5 ∧ p2)) ∧ False) ∧ p1) ∧ ((False → p3) ∧ True)) ∨ p3)) ∨ ((True ∨ False) ∨ p3)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39849246948499166512605580134 : (((p1 → ((p2 ∧ (p1 ∧ p1)) ∨ (((p3 ∧ p5) ∨ ((((p5 ∨ p4) ∨ (p4 ∧ p2)) ∨ False) ∧ ((p2 ∨ p1) ∨ p2))) → p3))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



