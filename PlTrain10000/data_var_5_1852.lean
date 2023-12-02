variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260386022908715158740869094881 : ((p2 → p5) → (False ∨ ((((p5 ∨ (p1 ∨ ((p3 → p4) → (False ∨ p2)))) ∧ (p5 ∧ ((p4 ∨ ((p2 ∨ p4) → p2)) ∧ p3))) ∨ p2) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h5.left
        let h23 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h28 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h29 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h28
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h30 := h1 h29
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167373013535219981564588397773 : (((((p1 ∨ p5) → (p3 ∧ True)) ∨ (((p4 → p3) → (p3 ∧ (p4 ∨ p2))) ∧ False)) → p5) → ((False ∨ (p4 → (True → (p3 ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92619284639354716636887106420 : (((False → p1) → (((((p3 ∨ False) ∨ True) → (p1 → False)) → False) ∧ ((p1 ∧ p2) ∧ ((p3 ∧ ((p1 ∨ p1) → (False ∨ p2))) ∧ False)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698776148148670128052217716294 : (((((p4 → p5) ∨ (False ∧ ((p2 ∧ p4) ∨ ((True → True) ∧ p2)))) ∨ (p1 ∨ ((p5 ∧ (p3 ∧ p5)) → (p1 → (p2 → (p3 ∨ p1)))))) ∨ p1) ∧ True) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178151734406367429489811094900 : (((((p1 ∨ p1) ∧ p1) → ((((p5 ∧ p3) → p3) ∧ p1) ∧ False)) → p4) ∨ ((p3 ∧ p5) ∨ (((True ∨ (p5 ∧ (False ∧ True))) ∨ p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628943129840606925681161028848 : (((((((((p4 ∨ (p1 ∨ ((p1 ∧ p3) ∨ False))) → ((True ∧ (True → False)) ∧ False)) → p4) ∨ (p1 → (True ∧ p2))) ∧ p5) ∨ True) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117360096519203379584155700713 : ((False ∧ (False ∨ ((p1 → p5) ∨ (((((p2 → p4) ∨ (False ∧ (p5 ∨ (p2 ∧ p5)))) ∨ p2) → ((p1 ∨ p3) ∨ p3)) ∧ p2)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148106655801326658910082245754 : ((((p2 ∧ ((p5 ∧ ((p1 → True) ∧ (p3 ∨ p1))) ∨ (p3 ∧ p4))) ∨ (True ∧ (p1 → p3))) → (p5 ∧ p3)) ∨ (True ∨ ((p1 → False) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208304502595512562425773372749 : (((p5 ∨ False) ∧ ((True ∧ True) → False)) → (((((((p4 ∨ ((p5 ∨ p4) → p5)) ∨ p4) ∧ p5) ∧ p1) ∨ p3) ∧ (p3 → False)) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328163340646666251561199727516 : (True → (((((p4 ∧ p2) ∨ ((p5 ∨ (p3 ∨ (((True ∨ (True → (True → p2))) ∨ True) ∨ p3))) → True)) ∨ p1) ∨ p5) → ((p4 → p5) ∨ True))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698393357361973723947976046379 : ((((((p1 ∧ p4) ∧ (p3 ∨ (True → (False → p2)))) → (False ∧ p4)) ∨ (p1 → (p2 → (p5 → ((((p5 → p2) → p1) → p3) ∨ p2))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65543654029795950590307811821 : ((p3 ∨ (True → (((p2 ∧ (p1 ∨ (((p5 ∨ True) → (True ∧ p2)) ∧ ((p5 → (p1 ∧ (p1 ∧ p5))) ∧ p1)))) ∧ p2) ∨ (True ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_746414079089352694291164347461 : ((((p2 ∨ p2) → ((p1 → (((((p4 ∧ ((p1 ∨ p3) ∨ False)) ∧ p5) ∨ True) ∨ True) → (((p4 ∨ (p2 ∨ p4)) → p3) ∨ False))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137974088148881065520304675276 : ((p5 ∨ ((p2 ∨ (p2 ∧ ((p2 → p2) ∧ (True → p3)))) ∧ ((p1 ∨ (((p3 ∧ (False ∨ p3)) ∨ True) ∨ True)) ∨ True))) ∨ ((True ∧ True) ∨ p4)) := by
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
theorem thm_5_vars_196985583234667964155783383193 : (((((False ∧ False) → (True ∨ True)) → False) ∨ True) ∨ (p4 ∨ ((p5 ∨ ((False ∧ (False → (True ∧ False))) → p1)) ∧ (p5 ∧ ((p1 ∨ p5) ∧ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42291883901903070419629281469 : (((p2 ∧ ((p5 ∧ ((p4 → p5) ∨ (((p3 → (False ∨ p5)) ∧ True) ∧ (((False ∨ (False ∨ p3)) → (False ∨ p2)) ∨ p4)))) ∧ p1)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856819729937724786764487421094 : (((((False ∧ ((False ∧ ((False → True) ∧ ((((p4 ∧ True) ∧ (True → p4)) ∧ p2) ∧ (p2 ∨ ((True ∨ p5) ∨ p3))))) ∧ False)) ∨ True) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((False ∧ ((False → True) ∧ ((((p4 ∧ True) ∧ (True → p4)) ∧ p2) ∧ (p2 ∨ ((True ∨ p5) ∨ p3))))) ∧ False)) ∨ True) := by
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
theorem thm_5_vars_148086898885741656210814394895 : ((((p5 → (p5 ∨ ((p3 → (p3 ∧ (p2 → (p2 → p2)))) ∨ (True → (True ∨ p1))))) ∨ p5) → (p5 → p2)) ∨ ((p1 ∧ (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38982697230780788630294686985 : ((((p4 ∧ False) ∧ ((p3 ∧ ((((p3 ∧ ((True → ((True ∨ p2) → p4)) ∨ False)) → p4) → p5) ∧ (p5 ∨ p4))) ∨ (p5 → p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667208667498253635406078029505 : (((((p1 ∧ p4) ∧ ((((p5 ∨ p1) ∧ (p1 ∨ (p3 ∨ p5))) → (((p1 ∨ (p2 → True)) → True) ∨ p1)) → False)) ∧ (p2 ∨ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693623205031205200815471554461 : (((((((((p5 ∨ (p2 → p3)) ∨ (False → p4)) → False) ∨ p1) ∨ p5) ∨ True) ∨ ((p2 ∧ ((p1 ∨ False) ∧ (p4 ∧ (p4 ∧ p5)))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_138901258161799389450322795198 : (((False → (p5 → ((p5 ∧ ((p4 ∧ p3) ∧ ((p5 ∨ (p2 ∧ False)) ∨ p3))) → (True ∧ ((False → True) → p1))))) ∧ p4) → (p1 ∨ (True ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166644179554833083467207547351 : ((p1 → ((False ∧ ((p2 → (p1 ∨ p5)) ∨ (((False → False) ∨ p2) ∧ p2))) ∨ (p1 ∧ p4))) ∨ (p5 → (p3 ∨ (True ∨ (True ∧ (p2 ∧ p3)))))) := by
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
theorem thm_5_vars_114313374497922843901635875308 : ((((False ∨ (p3 → (p3 → p4))) ∧ ((((((p2 → False) → p4) → p4) ∨ p1) ∧ p4) ∨ True)) ∧ (p5 → (p3 ∨ (False ∧ True)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158362180474878802546155439623 : (((p1 ∨ p5) ∧ ((p2 → ((p1 → (True ∧ ((p3 ∧ False) ∨ p3))) ∨ ((p2 ∧ p1) ∧ False))) ∨ p2)) ∨ (p2 ∨ ((True ∨ (p5 ∧ p2)) ∨ p4))) := by
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
theorem thm_5_vars_68823404484305526797613379760 : ((p4 → ((p3 ∨ (p2 → False)) ∨ (p2 ∨ ((p2 ∨ (((p2 → p1) ∧ p3) ∨ (p3 ∨ (((True ∧ (p3 ∧ p2)) → False) ∨ p1)))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201836567109534142090229607011 : ((((p1 ∧ p2) ∨ (True ∧ False)) ∨ True) ∧ ((p3 → ((True ∨ True) → (((((p4 → (p5 ∧ p2)) ∨ False) ∨ (False → p3)) ∧ False) ∨ p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87027750253415473315899338605 : ((((False → ((p2 → p2) → (True ∧ p2))) ∨ p1) → (((p4 ∨ p2) ∨ p4) ∧ (((True → False) ∨ (((p1 ∨ True) ∨ p4) ∨ False)) ∧ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → ((p2 → p2) → (True ∧ p2))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685160111481765656539460107744 : ((((p4 ∨ (((p2 ∨ ((False → p5) → False)) ∨ (p4 → ((p2 ∨ p2) → (p1 ∧ p3)))) ∧ False)) ∨ ((((False → p5) → p5) ∨ p5) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_247862679228594681511446128546 : ((p1 ∨ p2) ∨ (((False ∨ p3) ∧ p5) ∨ (False ∨ (((p2 ∧ ((((p1 → False) ∧ (p3 → p4)) ∧ p1) ∨ False)) ∧ False) → ((p5 ∨ False) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225763294419835788394531560892 : (((p5 → True) ∧ p5) ∨ (True ∧ ((p2 ∨ (p5 ∨ ((p1 → ((p2 → p1) → True)) → (((p2 ∧ False) → p1) → (p2 ∨ p2))))) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_26729065516537379746575067334 : (((p5 ∧ p3) ∨ (p3 ∨ (p5 ∨ (((False → p3) ∨ p1) → ((True ∨ False) → ((p2 ∨ False) → ((p5 → (p1 ∨ (True ∧ p5))) ∨ False))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206012630872283420052707445572 : ((p2 ∧ ((p3 ∨ (p1 → p2)) ∧ p3)) ∨ ((((False → p2) → ((False ∧ ((p1 ∨ (p1 ∧ ((p5 ∧ p3) ∨ p1))) ∨ False)) ∧ True)) ∧ p4) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41888475696038269921160599812 : ((((p5 ∨ (p5 → False)) ∨ (p5 → (p3 ∧ ((((p2 ∨ (True → (False ∨ p1))) ∧ ((p5 ∧ p3) → p1)) ∧ (p1 ∨ True)) ∧ True)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111877890272806816727688872146 : (((((p5 → (((True ∨ (p2 ∨ ((p1 → p1) → p4))) ∧ p2) → p3)) ∨ (p2 ∧ p5)) → (p2 ∧ ((True ∨ p1) → p4))) ∨ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251538214310272364082559090960 : ((p3 → False) ∨ (((True ∧ ((p2 ∨ ((p5 ∧ p1) ∧ p1)) ∧ (True → p4))) ∨ (True ∨ (p5 ∨ (((p2 → (p4 ∧ p2)) ∨ False) → False)))) ∨ p1)) := by
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
theorem thm_5_vars_57095189852815827303957692738 : ((((p4 ∧ p3) ∧ p3) ∨ (((p5 → p1) ∧ (((False ∧ (((p3 ∧ p2) → p2) ∧ ((p5 ∧ p1) ∧ p5))) ∨ True) → (False ∧ True))) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ (((p3 ∧ p2) → p2) ∧ ((p5 ∧ p1) ∧ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178749801329689040094477144335 : ((((p2 ∧ p2) ∧ True) ∧ ((p1 ∧ ((p4 → p1) ∨ p3)) → (p4 ∧ p1))) ∨ (True ∨ (((True ∧ False) ∧ p5) ∨ (True ∧ ((False ∧ p2) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140256905939555126365514133074 : ((((p3 ∨ ((p1 ∧ (((((False → p5) → (False ∨ True)) ∨ p2) → p4) ∨ False)) ∧ p2)) ∧ True) ∧ ((p4 ∧ p2) → p5)) → ((p5 → p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303714878628931556571535527322 : (p1 ∨ ((((True → (p1 ∨ ((True ∨ ((p1 ∨ p2) ∧ p4)) ∨ ((True ∧ (p5 ∧ p5)) ∨ (((p5 ∨ p4) ∧ p5) ∨ True))))) → False) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55425455454592573488646578535 : ((((p3 ∨ (p3 ∧ (False ∨ p2))) ∨ p1) → (p5 ∨ (((False ∨ (p1 → (True ∨ True))) ∧ ((p5 → (p4 ∧ False)) ∨ (False → p4))) ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117642573025119049316650551417 : ((p3 ∧ (((True ∨ ((((p4 → (True ∧ False)) ∧ False) ∨ (p4 ∨ (p2 ∨ p5))) ∧ p2)) → ((False → (p4 → p2)) ∧ p4)) → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166099338619655560007821659785 : (((p1 → p2) → ((((p4 ∧ p4) → p4) ∨ True) ∧ (p5 ∨ (((True ∨ True) ∨ p2) → p5)))) ∨ (p3 → (((True → p1) ∧ p5) → (p5 → p1)))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161887101537514571545095687611 : ((False → ((True ∧ p3) → ((((((True ∧ p3) ∨ p2) → p5) → (p4 → p2)) → p5) ∧ (p3 → p1)))) → (p1 ∨ (((p3 ∧ False) → p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628309586416632313884761044394 : ((((((p2 ∨ p4) → (False → (((p1 ∧ True) → ((True → (True → (True ∨ (p4 → False)))) → p5)) ∨ ((True → p5) ∨ False)))) ∧ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114933214631893507277961990187 : (((((True → p4) ∧ (((False ∨ p1) → True) → p5)) → (True ∨ (True ∧ p5))) → (((p2 ∧ p3) → ((True → p5) ∧ p3)) ∨ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626891462991176807967914922040 : ((((p5 → (p5 ∧ (((((p3 ∨ True) → (p2 → (p3 ∨ ((p4 ∧ True) ∧ False)))) ∧ (p4 → True)) ∨ (p2 → p4)) ∧ (p5 ∨ p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160679812902294256487353874502 : ((((p5 ∨ (p4 ∨ (False ∧ (p5 ∨ p5)))) → p1) ∧ ((p5 → True) ∧ (((p2 → p2) ∧ p2) ∨ p1))) → ((((p5 ∨ p1) → p1) → False) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p5 ∨ p1) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p5 ∨ (p4 ∨ (False ∧ (p5 ∨ p5)))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h10
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54930452972497711215376304206 : ((((p5 ∧ (p2 ∨ (False → p2))) → p5) ∧ (((p1 → ((((p4 → p4) ∨ ((p2 ∨ p2) → p4)) → False) ∧ p5)) → (p2 ∨ p1)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53291341205192337628343190444 : (((False ∨ ((((True ∨ True) ∨ p2) → False) ∨ (p1 ∨ (p3 → True)))) ∨ ((p4 → (False → ((False ∧ p3) ∨ (p2 ∧ (p4 ∨ p2))))) ∧ p1)) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172819983347532467407536525211 : ((True ∧ ((((p3 ∧ p4) ∨ p3) ∧ False) ∨ (((p5 → (p1 ∨ p3)) ∨ p4) ∧ False))) ∨ (((p4 ∨ (False → False)) ∨ (True → (p4 → p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_684753627936762626854533160974 : (((((True ∧ p3) ∨ (p4 ∨ (False ∨ (p4 ∧ ((p4 → (p2 ∧ True)) → ((p5 → p2) ∨ False)))))) ∨ (p2 ∨ (p4 → ((p2 → p1) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40584304748624677047447478470 : ((((((((False → p2) ∨ True) ∧ (((True ∨ (p5 ∧ p1)) → True) → p3)) ∧ ((p1 ∨ p3) → ((p4 ∧ p4) ∧ True))) ∧ p1) → p3) ∨ p1) ∨ p4) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((True ∨ (p5 ∧ p1)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : ((True ∨ (p5 ∧ p1)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h15 := h7 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340826756087551683738203881443 : (p2 → (((False ∨ (((p5 ∧ ((p1 → (((True ∧ True) ∧ ((p3 ∧ p2) ∧ (p3 ∨ p3))) ∨ p1)) ∧ p4)) ∨ p3) ∨ True)) ∨ (True ∧ p5)) ∨ p4)) := by
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
theorem thm_5_vars_323656681460028047744622036410 : (p5 ∨ (((((p5 ∧ (p4 ∨ (p4 → False))) ∧ (((p3 ∧ p1) ∨ p1) ∧ False)) → (False ∨ (p4 ∨ p4))) → p5) ∨ (True ∨ ((p5 ∧ p4) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301563982551855933560400100729 : (False ∨ ((False ∨ (True → p4)) ∨ (((((p3 ∨ False) ∨ p5) ∨ (((p5 ∨ (p5 ∨ p2)) ∧ p3) ∧ (False → p4))) ∧ (p5 ∧ (p5 → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314778715283889694320224106869 : (p3 ∨ (((False → ((p5 ∨ p5) ∨ True)) ∨ (False ∧ (False ∧ ((p5 ∧ p5) ∧ p4)))) → (p1 ∨ ((((p4 → p2) → (p1 ∨ p1)) ∨ p1) ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56112010754501989335304283048 : ((((False ∧ p5) ∨ (p5 ∧ p1)) ∨ ((p2 ∧ (p4 ∨ (((((False ∨ (p3 ∧ p1)) ∨ p5) → False) ∨ True) ∨ (True ∨ (p5 ∧ False))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186685010139484203269731189418 : (((p5 ∨ ((True → True) ∧ (p5 → False))) ∧ (False → (p3 ∧ p1))) → ((p2 → (p3 ∧ (p2 ∨ False))) ∨ (((p5 ∨ True) ∧ (p1 ∧ p5)) → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h19.left
      let h25 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672438462292968652246327119422 : ((((((False ∨ p3) → (True ∨ (((p3 ∨ (p4 ∧ (p3 → False))) ∨ True) ∨ ((p4 ∧ p5) ∨ (p4 ∧ p4))))) → p1) → ((True ∧ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312964051248393049763272485365 : (p3 ∨ (((((p1 ∨ p2) ∨ ((p2 ∨ p2) ∧ (((True → ((p3 ∨ p2) ∧ (True → (False → p3)))) ∨ True) ∨ True))) → (p5 ∨ True)) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110806510303681646294286126438 : ((((((((((((p3 ∧ True) ∧ p5) ∧ True) → p4) ∧ p5) ∨ True) → p5) ∨ p3) → (((p5 ∧ False) → False) → p3)) ∨ True) ∧ True) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92727283262788811261375485782 : (((p3 → True) → (True ∧ (((p5 → (((True ∧ (p3 → p1)) ∨ p3) → (((p1 → p3) → True) ∨ (p4 ∨ (p5 ∨ p3))))) ∧ False) ∧ True))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351918209925854170172231215697 : (p4 → ((p5 ∧ ((p1 ∨ (((p5 ∨ p1) ∨ p2) → False)) ∨ p5)) ∨ ((p4 ∧ (p5 ∧ (True ∧ (False ∧ False)))) ∨ ((p4 ∨ (True → p4)) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676597619706261452048836022162 : ((((p2 ∧ ((((p5 → (p1 ∨ True)) ∨ (False ∧ p2)) ∧ (p4 ∧ p3)) ∨ (True ∧ (p1 ∨ (p3 → True))))) ∧ ((p2 → (True → False)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405457241239701333520426455902 : (((((((p2 ∧ p3) ∨ False) ∨ ((((True → p1) ∨ (p2 ∧ (p2 ∨ p1))) ∨ (p4 → ((False ∧ p5) → (p3 ∧ p2)))) ∨ p3)) → False) → False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ p3) ∨ False) ∨ ((((True → p1) ∨ (p2 ∧ (p2 ∨ p1))) ∨ (p4 → ((False ∧ p5) → (p3 ∧ p2)))) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180945308989363813932417100471 : (((p1 ∨ p2) ∧ ((p3 ∧ p4) ∨ (((p2 ∨ p1) → p2) ∨ (p2 ∨ True)))) → ((p4 → ((p1 ∨ p5) ∨ (p3 → (False → (p5 ∧ p3))))) ∨ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h19
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h24
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h27
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h29
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h31
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Implications on the right can always be decomposed.
          intro h33
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h33
          -- False on the left can always be used.
          apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161470899187757725898279354414 : ((p3 ∧ ((p4 → ((p2 ∧ False) ∧ p5)) ∧ ((((((p2 ∨ True) ∧ p5) → p1) → p5) → False) → False))) → (p1 ∨ ((p1 → (True → p4)) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61529670613953367581912306423 : ((p1 ∧ ((False ∧ ((((p5 → (False → p5)) ∨ ((False ∧ p3) ∨ True)) ∧ p2) ∨ p1)) ∨ (((p3 ∨ ((p5 ∨ p2) ∧ p2)) → p2) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184315773839036764064011472178 : ((((p4 → p3) ∧ ((False → (True → (p3 ∧ True))) ∨ p1)) → False) ∨ ((p2 ∨ (((True ∨ (p4 → p5)) ∨ p1) ∧ False)) → (False ∨ (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
        -- False on the left can always be used.
        apply False.elim h5
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228541241483300039409158567118 : ((p1 ∨ (p3 ∧ p5)) ∨ (p4 ∨ ((((False → (True ∧ p1)) ∧ (((p4 ∧ p4) → (p2 ∨ (p5 ∨ p2))) ∨ (p2 ∨ p1))) ∨ (p4 → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18957636576029927090574567917 : (((p5 ∨ (((((p4 ∨ p3) ∨ False) → False) → p1) ∧ ((p2 ∧ p2) ∧ (True ∨ (p4 ∨ True))))) ∨ (((p1 ∧ p2) → (p1 → p2)) → True)) ∧ True) := by
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
theorem thm_5_vars_176302520089636640434703208727 : (((p4 ∧ ((p5 ∨ True) → (((p3 ∧ p3) ∨ p5) ∨ p2))) ∨ (True ∨ p1)) ∧ (p4 → (((p5 → ((p5 ∧ (p1 ∨ p5)) → False)) ∧ p3) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136178833215149345983280896666 : ((((((p1 ∧ p5) ∧ p1) ∧ p3) → p3) ∧ (False ∨ (((((False ∧ (p3 ∧ p5)) ∨ p3) ∨ p2) ∨ (False ∧ p1)) ∨ True))) ∨ (False → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589531914584122348186790252874 : (((((((False ∧ (True ∨ (p3 ∧ ((((p3 ∨ p5) ∧ (True ∨ p2)) ∨ (((p2 ∧ p1) ∨ p1) → p3)) ∨ True)))) ∨ True) → p1) → False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179170532507196680035446794007 : ((p2 ∧ (p2 ∨ ((p1 → ((p5 → p5) ∧ p1)) → ((p3 ∧ p2) → True)))) ∨ (((False → (p3 ∧ ((p5 → p3) ∧ p3))) → p3) → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p3 ∧ ((p5 → p3) ∧ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158454611249140834628210400966 : (((True → p2) ∨ ((p4 ∧ (p2 ∨ True)) ∨ (((p2 ∨ False) ∧ ((p3 ∧ p1) ∧ p3)) ∨ (False → p4)))) ∨ (p5 → (((p3 → p2) ∧ p1) ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618229254129604300107453088028 : (((((((p5 ∨ p2) → False) ∨ p1) ∨ (((((p1 ∨ p2) ∨ True) ∧ False) ∧ p1) ∧ (((p1 → ((p2 ∧ False) ∨ p5)) → True) ∧ True))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_317879451470246919200160941623 : (p4 ∨ (((p4 → p1) → ((((True ∧ (p2 → (p4 → ((p5 → p2) ∧ True)))) ∨ ((True ∧ (p4 ∨ p3)) ∨ p1)) ∨ False) → (p1 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184758005653674601623531608940 : (((p1 ∧ (p1 ∨ (p4 ∧ p3))) ∧ (((False ∧ True) ∨ True) ∧ p5)) ∨ (p1 → (((True → (p3 ∨ (p2 → p5))) ∨ p1) → (p2 → (p1 ∧ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257870979379993210106283542577 : ((p4 ∨ True) → (((False ∨ False) ∨ (((((True ∨ False) → p5) → (p1 → p2)) ∧ ((p1 → p2) ∧ p5)) → False)) ∨ ((p1 ∧ (p2 → False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187743478633547906890747914106 : ((p2 → ((((p1 ∧ ((True ∨ True) ∧ p2)) → p4) ∧ True) ∧ p2)) → ((((False → (False ∧ (p3 → p3))) ∨ p2) → (p4 ∧ p5)) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153083899588854468362135568962 : ((p3 ∧ (True ∧ (p3 ∧ (p2 ∧ ((p2 ∨ False) ∧ (((p3 ∨ False) → False) ∧ (((p4 → p4) ∨ False) ∨ p4))))))) → ((p1 ∨ p3) ∧ (True → p1))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h22.left
  let h24 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h28.left
  let h30 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h36 : (p3 ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h37 := h32 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
      have h40 : (p3 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h32, we can now drive its conclusion.
      let h41 := h32 h40
      -- False on the left can always be used.
      apply False.elim h41
  case inr h42 =>
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723972316753320295757337058601 : ((((False ∧ (False ∨ p2)) ∧ (((p5 ∧ False) ∧ (p2 ∨ (p5 ∨ (((False ∧ (True → ((p4 ∧ (p1 ∧ p2)) → p3))) ∨ True) ∨ p4)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114540564588443658204085806991 : (((p4 → ((p4 → (True ∧ ((False ∨ p1) ∨ ((p4 → ((p1 → p5) → p4)) ∨ p2)))) → p4)) → (p5 → ((p1 ∨ p1) ∧ p2))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353187821114163060641585550712 : (p4 → (p4 ∧ (((p3 ∧ ((p5 ∨ p2) ∧ (False → (False ∧ p5)))) ∨ (False ∨ ((p5 ∧ True) ∨ p5))) ∨ ((p1 ∧ ((p1 → p4) → False)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48550660542929891888174822756 : ((((((p5 ∧ (False ∨ ((p3 ∨ True) ∧ p1))) ∨ (((p3 ∨ p2) → (True → (p1 ∧ p3))) → p4)) → p5) → False) ∧ (True ∧ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145940106423688574406100003494 : ((True ∧ ((((p1 ∨ False) ∨ True) → ((True ∨ (p5 ∨ p5)) → (p2 ∨ p1))) ∨ (((p4 ∧ p5) ∧ p1) ∨ True))) ∧ ((p1 → p2) ∨ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67341297119816830617402438877 : ((p1 → (((((((p5 → p5) ∨ False) ∧ p5) → p4) → True) ∧ (p2 ∧ ((((True ∧ p3) ∨ (p4 ∨ (p5 → False))) ∨ p5) ∨ p3))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341075413035810526098826921711 : (p2 → ((True → (((((p5 ∧ (True → p3)) → p3) → (False → (((p3 ∨ False) → p1) ∨ (False → (False ∧ (p2 ∧ p4)))))) ∨ p4) → p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39730206102561368229983704186 : (((p5 ∨ ((p3 → ((p3 ∧ p5) → p1)) → (False ∧ (p3 ∨ (p2 → (((((True → (p5 ∨ p5)) → p5) ∨ p2) → p2) ∨ p1)))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148228777366549501073561158477 : (((((p4 → ((p1 ∧ p2) ∧ ((p3 ∨ (p5 → p2)) ∧ True))) ∧ (p5 → p5)) → p3) ∨ ((p5 ∨ True) ∧ p5)) ∨ (False → ((p4 ∧ p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199471878051327519301855649308 : (((p1 ∨ ((p4 → p1) ∨ (p3 ∨ p4))) ∨ p5) → ((p4 → ((False ∧ p1) ∨ p1)) → ((p2 ∧ ((True → ((p3 ∧ p5) ∧ True)) ∨ p3)) → p3))) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h10 := h6 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- We need to get the left conjuct of h11 based on <expert-advice>.
        let h12 := h11.left
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h16 := h6 h15
          -- We need to get the left conjuct of h16 based on <expert-advice>.
          let h17 := h16.left
          -- We need to get the left conjuct of h17 based on <expert-advice>.
          let h18 := h17.left
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h22 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h23 := h6 h22
            -- We need to get the left conjuct of h23 based on <expert-advice>.
            let h24 := h23.left
            -- We need to get the left conjuct of h24 based on <expert-advice>.
            let h25 := h24.left
            -- One of the premise coincides with the conclusion.
            exact h25
    case inr h26 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h28 := h6 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h38 =>
            -- One of the premise coincides with the conclusion.
            exact h31
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207439393574793441953790297553 : (((p2 ∨ (p5 ∨ (p4 ∧ p5))) ∨ True) → ((p2 → ((p3 ∧ (p1 ∧ (p3 ∨ (p3 → (p2 → p5))))) ∨ p4)) ∨ (((p3 → p5) → True) ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241866905619298309720736652246 : ((p1 → p1) ∧ (p4 ∨ ((True ∧ ((True ∨ p3) ∧ ((p1 → p4) → (p4 ∧ (p4 ∨ p5))))) ∨ ((p1 → (p1 ∨ (True → (False → p5)))) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300056535551108046035635613792 : (False ∨ ((((True ∨ p1) ∧ (((((p4 ∨ p2) → ((p5 ∧ p2) ∧ (False → p2))) ∨ p5) ∧ ((True ∧ p2) ∧ p2)) → p1)) ∧ p5) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225941811973709942220018239968 : (((p2 ∧ p3) ∨ p3) ∨ (p2 → ((p5 ∨ (p1 → ((p4 ∨ p1) ∧ p1))) ∨ ((p3 → (((p3 → p1) ∧ p1) → (True ∧ (p5 → False)))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50875032464829163474362830414 : (((((True ∧ (((p1 → True) ∨ (p2 ∨ ((p1 ∧ (p2 ∨ False)) ∧ p3))) ∨ p1)) ∧ p4) → p5) ∧ ((p3 ∧ (False ∧ p4)) ∨ (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748940804284507794781874439716 : ((((p4 → p3) → ((p5 → (p1 → ((True ∨ ((p5 ∧ (((((p1 → p4) ∧ False) ∨ (p1 → p3)) → False) ∧ p5)) ∧ True)) ∧ p4))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149884066781129819818356980229 : ((p2 ∨ ((True ∨ (p3 → ((p4 ∨ True) → p4))) → ((p4 → (p4 → (p3 ∨ p2))) ∨ (p2 ∨ (p4 ∨ p3))))) ∨ ((False → True) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



