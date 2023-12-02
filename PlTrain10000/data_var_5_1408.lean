variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313007947046947505952371526707 : (p3 ∨ (((((p4 → ((True ∧ ((p5 ∨ (False → p4)) → p1)) → True)) ∨ True) ∧ (p4 ∨ (((False ∨ False) → p5) → (p5 ∨ False)))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53307610158355114137829046199 : (((p5 ∨ (p5 ∨ ((((p5 ∨ p3) ∧ (p4 → p2)) → p4) ∧ False))) ∨ ((p3 → ((p4 ∧ (True → True)) → p3)) ∨ (True ∨ (True ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46553825548951481620484965347 : ((((True ∨ True) → ((p1 ∧ (((True ∨ ((True → (False ∨ ((p5 ∨ False) ∧ p4))) → p4)) ∨ p5) ∨ (True ∧ p3))) ∨ p5)) ∧ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158406452634975922773844503326 : (((False ∧ False) ∨ (((((False ∧ p4) → (False ∧ (p5 ∨ (False ∧ (p3 ∨ p3))))) → p4) → p3) ∨ p1)) ∨ (p4 ∨ (p2 ∨ ((p3 ∧ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_704763168080215548006691353925 : ((((p4 ∧ (((p1 ∨ (p1 → p2)) ∧ p4) → (p1 ∨ p5))) → (((((p3 ∨ (p5 ∨ (p3 ∨ p5))) ∧ p2) ∨ (True → True)) ∧ True) ∨ False)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139454513977675486146870940688 : ((((((p5 → (p3 ∧ p5)) ∧ ((False → (((p4 → (False ∨ True)) ∧ p1) → True)) ∨ False)) → (p2 ∧ p2)) ∨ p5) → False) → (p4 ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 → (p3 ∧ p5)) ∧ ((False → (((p4 → (False ∨ True)) ∧ p1) → True)) ∨ False)) → (p2 ∧ p2)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148827018623251026676092406681 : (((p1 → (p2 ∧ ((p1 ∧ False) ∧ p3))) → (((((False ∨ p3) ∨ p3) → True) ∧ ((True ∨ False) ∧ False)) ∨ p1)) ∨ (True ∨ (p4 ∨ (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151873775128522027524673031512 : (((p2 → ((p1 ∨ ((((p2 ∧ (p1 → p2)) ∧ p2) ∧ p5) ∧ True)) → False)) ∨ (((p1 ∨ p3) ∨ p3) ∧ p3)) → ((p5 ∨ (p1 → p4)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178818980565269355816160879564 : (((p2 ∨ (p4 ∨ p4)) ∨ (False ∧ (p1 ∧ ((False → (p1 → p5)) → p4)))) ∨ (True → (False ∨ (((p3 ∨ (True → p5)) → (p1 → True)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342433972937398285270573330797 : (p2 → ((p4 ∧ (((False ∨ (p2 ∧ p3)) → (False ∧ (p1 ∧ False))) ∧ (p3 ∧ (p2 ∨ p3)))) → (((p1 → (p4 ∨ (p2 ∨ p2))) ∧ False) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h19 : (False ∨ (p2 ∧ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h20 := h14 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h23 : (False ∨ (p2 ∧ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h24 := h14 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h2.left
  let h27 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h29.left
  let h31 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h32 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h33 : (False ∨ (p2 ∧ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h34 := h28 h33
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h37 : (False ∨ (p2 ∧ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h36
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h38 := h28 h37
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191519845685850418394509679976 : ((False ∧ ((p4 ∨ True) → (p3 ∨ ((p3 ∧ p1) ∧ False)))) ∨ (p4 ∨ (False ∨ ((p2 ∨ p2) ∨ (p3 → ((True ∨ (p2 → p5)) ∨ (p5 ∨ False))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41501532160222275829055031783 : (((((False → False) ∧ ((p5 → p4) ∨ ((p2 ∨ p2) → (p1 ∨ p3)))) → ((p4 ∧ p3) → ((p3 → ((p1 ∧ p3) ∧ p2)) → False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116818025060890197064820476929 : (((p4 ∨ p2) ∨ ((((p1 ∧ (True ∧ (((p1 ∨ p4) ∧ p5) ∧ (p5 ∧ (p4 → False))))) ∧ True) → p1) → ((False → p1) → p5))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347205055638401655770147639544 : (p3 → ((p2 ∧ (((p2 ∨ ((p3 ∨ p5) → p2)) → False) ∧ (p4 → p1))) ∨ (p4 → (p5 ∨ ((((p2 ∧ p3) ∨ (p3 ∧ False)) → p3) → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174477848770468485588716590896 : ((((True → p2) ∧ ((p1 ∧ True) ∧ p1)) ∧ (((p1 ∧ p4) ∨ (p2 ∨ p1)) ∧ p3)) → ((p5 ∧ p2) ∨ (((p3 ∧ p1) → p3) → (p5 ∨ p3)))) := by
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
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136129505397097568691010642896 : (((((False ∧ ((True → p1) ∨ p5)) → p2) ∧ p2) → (p1 ∧ ((True ∧ (p4 ∨ ((p2 ∧ p2) ∨ p5))) → (p1 → p4)))) ∨ ((True → p5) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37335068601737930036602626499 : ((((((((p2 → (p3 → p5)) → p2) → p1) ∧ ((p5 ∧ (p3 → p1)) → (p3 → ((True ∧ p2) ∨ (False ∧ p5))))) ∧ p4) ∨ True) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52103142320520919762418497472 : ((((p1 ∨ (p4 ∨ ((((True ∨ (False ∧ (True ∨ True))) → False) → p4) ∨ True))) ∨ p2) → (((True ∧ (p3 → p4)) ∨ (p2 ∨ p2)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42328814224055464342461123493 : (((p3 ∧ ((((p2 ∨ ((p2 ∧ p5) ∨ (p5 → p5))) → ((((True ∧ (p1 → True)) ∧ (p5 ∧ p2)) → p3) ∧ True)) ∨ False) ∧ p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_513054003599618629610512747172 : ((((p5 ∧ p3) ∨ (((p3 ∧ p3) ∨ (False ∨ (False ∨ p4))) ∨ (((p5 → p2) ∧ (((p3 ∧ True) ∧ ((p1 ∧ True) → False)) ∨ p3)) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_343801305270257174125633532530 : (p2 → (p2 ∧ (((((False ∧ (p1 ∧ (p5 → (p3 → (p1 → p1))))) ∧ (p5 → (p1 ∨ p2))) ∧ False) ∨ (p3 → ((True → False) ∨ True))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_53930068154795388211483239180 : (((p5 ∨ ((p4 ∨ (True ∨ p4)) → ((True → True) ∧ p5))) ∨ ((p3 ∨ ((p1 → (True → p5)) ∨ (True ∧ (True ∨ p1)))) ∨ (p1 ∧ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690109177604978915982247309043 : ((((False ∨ (((((p2 → p2) → False) ∧ (p1 ∨ ((p2 ∨ p3) ∨ True))) ∨ p4) ∧ False)) ∨ ((p5 ∧ p4) ∧ (((True ∧ p4) ∨ True) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59234122605114084059873188179 : (((p2 ∨ p1) ∨ ((((p3 → p1) → ((True → ((False ∧ True) ∧ p3)) → (p1 → p2))) ∨ False) ∧ (p2 → (p1 ∨ (False → (p3 → True)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179347107831090114705013967252 : ((p1 ∨ (p4 ∨ (p3 → ((((p5 → True) → (False ∨ p4)) ∧ p2) ∧ p4)))) ∨ (p5 → (p5 ∧ (((False → (False ∧ (p4 ∧ True))) → p4) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676857156794480324319014302581 : ((((p3 ∨ (p3 ∧ (False ∧ (p3 → (((True → p1) → (p3 ∧ (((p4 → False) → False) ∨ p1))) ∧ p5))))) ∧ (False ∨ (p4 ∧ (p2 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134084772062599388813069552875 : (((((p1 ∧ ((p1 → p3) ∨ p5)) ∨ ((p1 → ((p5 ∨ p5) → (((False ∧ p4) ∨ True) ∧ True))) ∧ p5)) → False) ∨ p2) ∨ ((p2 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786422754838722239106607735969 : (((p4 ∨ (((p2 ∨ (False → ((p4 ∧ True) → (p2 ∧ p4)))) → (True ∧ (p4 → False))) ∨ (True ∨ (p4 ∧ (((False ∧ p2) ∨ p5) ∨ p5))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_69036778978497910968443867018 : ((p5 → (((True → (p4 ∨ ((p1 ∨ (False → (((p2 ∧ (p4 ∧ p5)) → p4) → (p3 → False)))) → p2))) ∨ ((p4 → p5) ∨ p4)) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157884517034939963847773850804 : ((((p5 ∨ p2) ∨ (p1 ∧ (p5 → (p4 ∧ (p4 → p4))))) ∨ (((p1 ∧ p5) ∨ (p5 ∧ p2)) → False)) ∨ (True ∨ (True → ((p2 ∧ False) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135664492119852386420452546327 : (((p2 ∧ ((p2 ∨ p3) ∧ (True ∧ (True ∨ ((((p3 → p1) ∨ False) ∧ p3) → p1))))) → ((p1 → p2) → (p4 ∧ p1))) ∨ (p2 → (p2 ∧ True))) := by
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
theorem thm_5_vars_228998971867386131349800292396 : ((p5 ∨ (p1 ∧ p1)) ∨ ((p4 → p5) ∨ ((p3 → (p2 ∨ ((False ∨ (p1 ∨ False)) ∨ ((p3 ∧ p2) ∨ ((False ∧ p1) ∧ False))))) → (p3 ∨ True)))) := by
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
theorem thm_5_vars_114721403688113642582766686961 : (((((True → (p1 ∧ (False ∧ (p1 ∧ (True ∧ (True → p4)))))) ∨ p5) → (True ∨ p5)) → (((True ∨ p1) ∧ p3) ∧ (False ∧ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186366170361404060322431584053 : ((((p5 ∧ True) ∨ ((p5 ∨ (p3 ∨ True)) ∨ (p4 → True))) → False) → ((((p3 ∨ p4) → False) ∨ p5) ∧ (((False ∨ p3) ∨ p2) ∨ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ True) ∨ ((p5 ∨ (p3 ∨ True)) ∨ (p4 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ True) ∨ ((p5 ∨ (p3 ∨ True)) ∨ (p4 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10352747398155576710671132681 : (((p5 ∨ (p5 ∧ ((((p5 ∧ True) ∧ (((p1 ∧ True) → ((p2 → (p1 ∧ ((False → p2) ∧ p1))) ∧ p1)) ∧ False)) ∧ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118801317483746467012659116077 : ((True → (((((p1 ∧ True) ∨ (((((p2 ∧ False) ∨ p3) ∧ p5) ∧ p1) → p3)) → p4) → (p3 ∧ (p1 → (p5 ∨ p4)))) ∧ p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147270904318811718184664042519 : ((((((((True ∨ (p5 → True)) ∧ (p2 ∧ p5)) ∨ p2) ∨ (p2 ∧ p4)) ∧ (p5 ∧ (p5 ∧ False))) ∨ p4) ∨ p5) ∨ (False → (p1 → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309800624614799140328273908761 : (p2 ∨ (((((p5 ∨ p4) ∨ p3) → (True ∧ (p5 → False))) → ((p5 ∨ (p4 ∧ (p1 ∧ (p1 ∨ False)))) ∧ True)) ∨ ((True ∧ p5) → (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53562494297385320916034406796 : ((((((True ∨ p5) → ((False → False) → True)) → p4) ∨ p5) ∧ (((((False ∨ ((True ∨ (p1 ∨ False)) → p2)) → p1) ∧ p3) ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113554322243606239774281935839 : ((((p4 → (p5 ∨ False)) → ((p4 ∨ (p2 ∧ False)) ∧ ((p2 → p2) ∧ (p3 → (p2 → (p1 ∧ (p4 ∨ p5))))))) ∨ (True ∨ False)) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67971857041599835133925203858 : ((p2 → ((p1 ∧ (p2 → p3)) ∨ (p1 ∨ (False ∧ ((p2 → p3) ∧ ((((p1 ∨ (p4 → p5)) → p5) → (p3 ∨ (p5 ∧ p5))) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231772527828390024435954300338 : (((p3 ∧ p4) → p3) → ((((False ∨ p4) ∨ p1) ∨ (((((p4 → p3) ∨ True) ∧ p4) ∨ (False → (False → p5))) ∨ False)) ∨ ((p5 → p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26994818166308873920558164891 : (((p5 ∨ p2) ∨ (((((p4 ∧ p2) ∧ ((p2 ∨ p4) → (p1 ∨ True))) → p1) → ((True ∨ (True → ((p2 → p4) ∨ p4))) → p1)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_191481678941680357972368535215 : ((True ∧ ((True ∨ (p5 ∨ False)) ∧ (p3 ∧ (p3 ∨ p1)))) ∨ (True ∧ ((True → (p1 ∧ False)) → (((p2 → (False → (p5 ∧ p3))) → False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343810434111231941975726524876 : (p2 → (p2 ∧ ((((p5 ∨ ((((True ∨ p3) → p4) ∧ p2) ∨ (p5 ∨ False))) → (p1 ∧ (False ∨ ((True ∨ p5) → p4)))) ∨ True) ∧ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52762223966582527658809493575 : (((((((p3 → False) ∧ p2) → p2) → ((p5 ∨ True) → (p5 ∧ p5))) → True) → ((((p5 ∧ p2) ∨ p2) ∧ (p2 → False)) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53145205961106182374575549323 : (((((((((True ∨ p4) ∧ p3) ∨ p3) ∧ p4) ∧ p1) ∧ p3) ∨ True) ∨ ((p3 ∧ True) → (p4 ∨ ((p2 ∨ (False ∨ p5)) ∨ (p1 ∧ p4))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41278942976689315733952004858 : (((((((p4 → ((((True ∧ (p4 → False)) → p4) → p1) ∧ False)) ∧ (p1 → p3)) ∧ p5) → p2) → (p5 → ((p4 → False) ∨ True))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65309809999792789167631307455 : ((p3 ∨ (((p5 ∨ (((p3 ∧ (p2 → p5)) ∧ (p1 ∧ (p5 → False))) ∨ (True ∨ False))) ∨ (p5 → (p2 → p4))) ∧ (p5 ∧ (p4 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230691126105831260299040871308 : (((p4 → p1) ∧ p1) → (((((True → (((False ∨ True) ∨ (p4 ∨ (False → p2))) ∧ ((p3 → p3) → p3))) ∨ (True ∨ p5)) → False) ∧ p4) → p5)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((True → (((False ∨ True) ∨ (p4 ∨ (False → p2))) ∧ ((p3 → p3) → p3))) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56947785276564932558116376488 : (((p1 ∨ (p2 ∨ p4)) ∧ ((((((p1 → False) ∧ ((p1 → (False → p2)) → (p4 → p2))) ∨ (p5 ∨ (False ∧ False))) ∨ p1) ∨ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219609256160123206910295997822 : ((True → (p2 → (p1 → p4))) → ((((((p3 ∧ p5) → False) → p3) ∨ ((p2 ∨ p5) → (True → ((p2 ∨ p4) ∨ p4)))) ∨ True) ∧ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656164076669962721912688968961 : ((((((p4 ∧ ((False ∧ ((p2 → p3) ∨ False)) → True)) ∧ (False → (p1 ∨ p4))) ∨ ((p4 → p5) → (p4 ∧ (p5 → p4)))) ∨ (p3 → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76307985717118580680898461809 : (((((p4 → ((True ∧ True) ∧ p2)) → ((((p1 ∧ True) → (p3 ∧ p3)) → p5) ∨ (True → (p2 ∧ (p2 ∧ p3))))) ∨ (False → True)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((True ∧ True) ∧ p2)) → ((((p1 ∧ True) → (p3 ∧ p3)) → p5) ∨ (True → (p2 ∧ (p2 ∧ p3))))) ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65744515019334125168073142240 : ((p4 ∨ ((p1 → (((p2 ∨ False) → (p5 → p3)) → (p1 → (p1 ∧ (p3 → (((p5 ∧ p3) → True) → p5)))))) ∨ ((p2 ∨ True) → True))) ∨ p4) := by
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
theorem thm_5_vars_358017213172212879109365036557 : (p5 → (False ∨ (False ∨ (p4 → (True → ((False ∧ (p1 ∨ (((p5 ∧ (p5 ∨ (((True ∨ False) ∧ p5) → (False → p1)))) → p2) ∧ p5))) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37505647915814013178926699919 : (((((True ∧ p5) ∨ (p4 → (((True → (True ∧ p5)) ∧ ((p3 ∧ p1) → True)) ∨ ((p2 ∨ ((True ∧ p1) ∨ p2)) → p5)))) ∨ False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633885481933410143631764284568 : ((((((((False ∨ True) ∧ ((p1 ∧ False) → (p2 → (p5 → (p4 → True))))) → ((True ∧ (p4 → p5)) ∧ True)) ∨ False) → (p2 → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62950287308968956804978120141 : ((p4 ∧ (p5 ∧ ((p5 ∨ p5) → (((p3 → p2) → ((False ∧ (p3 → (False ∨ p3))) ∨ (((p4 → p2) ∧ p5) ∨ p5))) → (False ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337962896949267324891730955080 : (p1 → ((p4 ∨ (((p4 → p1) → p3) ∧ (False ∧ ((True → p4) ∧ p4)))) ∨ (((p5 ∨ ((True ∧ False) ∧ ((p2 ∧ p4) ∧ False))) → p5) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230069320815138551706848990937 : (((p2 ∧ p2) ∧ p4) → ((((p1 ∧ (((((True → False) ∧ p3) → p5) ∨ (p3 → (True ∧ p3))) ∧ p2)) → p5) ∧ (p5 ∨ (p1 ∧ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194085509841010543051620678089 : ((True → (False ∧ (p3 ∧ ((p3 ∨ p5) ∨ (False ∨ p2))))) → (((p3 ∧ (p1 ∨ True)) ∧ ((((p5 ∨ p5) ∧ (True ∨ p1)) ∧ p5) ∨ p2)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39843081181113247616920567723 : (((p1 → ((p2 ∨ (p4 → (True ∨ ((p4 → (p5 ∨ p5)) ∧ ((p2 ∨ p3) ∧ p2))))) → (((p4 → (True ∧ p1)) ∧ p2) ∨ p4))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821430440217511479902643844902 : (((((True ∧ ((p5 ∧ (((False ∨ p4) ∧ True) → (False ∧ p4))) ∧ (p1 ∧ p1))) ∧ ((p5 ∨ False) → ((p3 ∧ (p2 ∨ p5)) ∨ False))) ∧ p4) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h9.left
  let h13 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h14 : ((False ∨ p4) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742645737783585569177727132818 : ((((p2 → p4) ∨ ((True ∧ ((((p1 ∨ (p3 → ((p5 ∨ (p4 ∧ p2)) → p4))) → p4) ∨ p2) ∧ (p4 → (p3 → False)))) → (p4 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117111362443000037935844370351 : (((p3 → True) → ((p4 ∨ True) → (((p5 → (((p2 → True) ∧ True) ∧ p5)) → p2) → (((p2 ∨ (p1 ∨ p1)) → p4) ∨ True)))) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_64481461416262476343098646540 : ((p1 ∨ (((False ∨ (p4 ∨ ((p4 ∨ (p5 ∧ p2)) ∨ (p2 → (p5 ∨ ((p1 ∨ p2) → False)))))) → p3) ∨ ((p1 ∨ (False → p1)) ∨ p5))) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246790340696718179678355171686 : ((p5 ∧ p5) ∨ (p2 → (p3 ∨ (((True ∨ p5) → (p4 → (False ∧ (((((p4 → p5) → ((p3 ∧ p1) ∧ p5)) ∧ p1) → p3) ∨ False)))) ∨ True)))) := by
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
theorem thm_5_vars_115300297678517245936790652606 : (((((p2 → ((p5 → (p5 → p2)) ∨ p2)) ∨ True) → p3) → (((p2 → (p1 ∨ p4)) → p4) ∧ (((False ∨ p2) ∨ p3) ∨ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192223650033804886652541713159 : ((((p5 → (p4 → (p3 ∧ (p3 → p1)))) → p1) ∧ p4) → (((((p3 → p2) ∨ (p2 ∧ ((p2 → p3) ∧ p5))) ∧ False) ∧ (True → p1)) ∨ True)) := by
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
theorem thm_5_vars_137291534749439649320058878480 : ((p2 ∧ ((p3 → (p5 ∨ ((False ∧ p5) ∨ (p4 → ((p1 → p3) ∨ ((p1 ∨ (True → p1)) → (p1 → False))))))) ∨ True)) ∨ (p1 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166313130217330058255926110972 : ((p5 ∧ (((p5 → (False ∧ ((False ∧ True) ∧ p4))) ∨ ((False → (False ∨ p4)) ∧ p3)) ∨ p3)) ∨ (False → ((p3 ∧ (p1 ∨ p2)) → (p2 ∨ p3)))) := by
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
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238343366102834810671735835905 : ((False ∨ True) ∧ (p2 ∨ (p3 → ((((False ∧ ((p3 → ((p1 ∨ p1) ∧ (p4 ∨ (p4 ∨ True)))) → p4)) → p5) → ((True ∧ p3) ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_779165574724931999909743157859 : (((p2 ∨ (((((((p1 ∨ (p1 → p3)) → ((p1 → False) ∧ (True ∧ p5))) → (p1 ∧ p2)) ∧ (p4 → p4)) ∧ p2) ∨ (False → False)) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41298350109138530419475191371 : ((((True ∨ (p4 ∨ ((p3 ∨ (False → False)) → (True ∧ ((True ∨ (p4 ∨ (p3 → p3))) ∨ p5))))) → (True ∧ (True → (p5 → p3)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734388858446928933685424248401 : ((((False ∨ p4) ∧ ((p4 ∨ (p1 → (True ∧ p4))) ∨ ((p1 → p2) ∨ (p5 → (((((p1 ∧ p4) → p2) ∨ p4) → (p3 ∨ p4)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614676583942595025007357769652 : (((((((((((((p3 ∨ False) ∨ (False → p2)) → False) ∧ True) ∧ p1) → p1) ∨ p1) ∧ p1) ∨ p4) ∨ (p2 → ((False ∨ False) ∧ p3))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_230985099046000115939147905619 : (((p4 ∧ p4) ∨ p3) → (((p1 ∧ ((p4 ∨ False) ∧ (p1 ∧ p3))) ∨ (True → (p3 ∨ ((p3 → ((p4 → (False → False)) ∨ p2)) ∧ False)))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643699243228381899531524562556 : ((((p5 ∧ ((((p3 ∧ ((False → ((p1 ∧ (True → p3)) ∧ (p4 ∧ (p1 → (p4 ∧ (p5 ∧ p5)))))) ∧ p3)) ∧ p3) → False) → False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165008004896896026188275368794 : ((((((p4 → p5) → (False ∧ False)) → False) ∨ ((p3 ∧ (p3 ∧ (p1 → p5))) ∧ True)) → p3) ∨ ((p5 ∨ (p1 → (p2 ∨ p2))) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308947077176895330360411087390 : (p2 ∨ (((((p1 → ((p3 ∨ True) ∨ ((p5 ∧ False) → False))) ∨ (p3 ∧ p3)) → False) ∧ (p2 ∨ (((p3 ∧ p4) ∧ p1) ∨ (p2 → False)))) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 → ((p3 ∨ True) ∨ ((p5 ∧ False) → False))) ∨ (p3 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((p1 → ((p3 ∨ True) ∨ ((p5 ∧ False) → False))) ∨ (p3 ∧ p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54647132051545971885854212645 : ((((((p1 ∧ (p5 → True)) ∨ p5) ∨ True) ∨ p2) → (((p5 → p4) → ((p1 → (((True ∨ p3) → p2) ∧ (p2 ∨ p4))) → p5)) ∨ True)) ∨ p2) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114342219990796355311021575580 : (((p2 ∨ (((p2 → False) ∨ ((((True → False) ∨ p1) ∧ p4) ∧ p3)) ∧ (False ∨ (p3 ∨ p2)))) ∧ (p4 → ((True ∨ True) ∨ p1))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116862792813010720284837154090 : (((p1 → p2) ∨ (False ∨ ((((p4 ∨ p2) ∧ (((False → p3) → p2) ∨ p3)) ∧ p3) ∧ (False ∨ (True ∨ (p5 ∨ (p1 ∨ False))))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52118960828287599757801999058 : ((((((True → True) ∧ False) ∧ ((p3 → ((p5 ∧ p2) ∨ (p5 ∧ p2))) ∧ p2)) → False) → (((p4 ∨ p2) ∨ (False → (p1 ∧ p1))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157624952031168449614453060982 : ((((p4 ∧ (p3 → (p1 ∨ (p2 ∧ False)))) ∨ (p3 ∨ (False → (p4 ∨ p4)))) ∧ (False → (False ∧ p3))) ∨ ((p1 ∨ (p2 ∧ True)) → (p2 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350300991334516817196290908825 : (p4 → ((p2 ∨ ((False ∨ ((False ∨ (p1 → p1)) ∧ False)) ∨ (((p1 ∧ ((p3 → p4) → (False ∧ p3))) → (False ∨ (True → p2))) ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41756698263946065952343490162 : (((((True ∧ (p1 ∨ False)) → p5) ∨ (((True ∧ ((((True → p2) → p2) → True) ∧ (True ∨ False))) ∧ p5) → ((p1 → p3) ∧ p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196925762228481738980836754254 : ((((True ∧ (False → (p1 ∨ True))) ∧ p2) ∨ False) ∨ (((((p5 ∨ (((p2 ∧ p3) ∨ True) → ((True ∧ True) ∧ False))) → p5) ∨ p4) ∨ p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∧ p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316438179141269794795076251115 : (p3 ∨ (p1 ∨ (((p5 → ((p2 ∧ p5) ∨ ((((p2 ∧ p1) → ((p5 → (False ∧ p2)) → False)) ∧ False) ∧ (p3 ∨ p4)))) ∨ True) ∨ (False ∧ p5)))) := by
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
theorem thm_5_vars_685085731457833955874806698097 : ((((p1 ∨ (((p4 ∧ (True ∧ (((p5 ∨ True) ∧ ((p3 ∧ p2) ∨ p1)) ∧ p3))) ∧ p5) ∨ True)) ∨ (p4 ∨ ((p4 ∨ p5) → (p5 ∧ p1)))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68869875949105914732525029610 : ((p4 → (False ∧ ((((((p5 ∧ (p5 ∨ p1)) ∨ p5) → (((False ∧ p4) ∧ p4) ∨ p5)) → (p5 ∨ p1)) ∧ ((p5 → p2) → p4)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744935830060112089792295032228 : ((((p4 ∧ True) → (((p2 ∨ (p3 ∨ True)) → ((p2 → p4) ∧ False)) → (((False ∧ (True → ((p4 ∧ p1) ∨ p5))) ∨ p4) ∧ (p4 → p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186178279652113848936341218074 : (((p1 ∧ (p3 → (p1 ∧ ((p4 ∧ (True ∨ p1)) ∧ p5)))) ∨ True) → ((True → False) → (p2 ∧ ((p4 → ((p1 ∨ p1) → (p3 ∨ p4))) ∧ p3)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h30 := h2 h29
      -- False on the left can always be used.
      apply False.elim h30
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h35 := h2 h34
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h37 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h38 := h2 h37
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47217621681434338784577135219 : (((((False → (((True → True) ∧ (p3 → p1)) ∨ p4)) ∨ False) → (False ∧ (((p1 ∨ (p3 → p4)) ∨ (p4 ∧ p2)) ∧ p2))) ∨ (p1 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165516318311926515028463060767 : ((((p2 ∧ ((p4 ∨ True) → (p1 ∧ p5))) ∨ (p4 ∨ p4)) → (p5 ∧ ((p4 ∧ p1) ∨ p3))) ∨ (True ∨ ((False → (p2 ∧ True)) ∧ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198265161332470084161349901593 : ((False ∧ ((p2 → ((False ∨ True) → p2)) → p4)) ∨ (p4 → (((p4 ∧ p3) ∧ ((p2 ∨ p5) ∧ p5)) ∨ (((p3 ∧ True) → False) ∨ (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_615884782643363416104368441281 : ((((((p5 ∨ True) → ((((p4 ∧ p2) ∨ p2) ∧ p2) → ((p5 ∧ p5) ∨ p1))) ∨ ((True ∨ p4) ∨ (False → ((p4 → p5) → p5)))) ∨ False) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209042589253473256554707112970 : ((p1 ∨ (((True ∧ p5) ∨ p3) ∨ p1)) → (((p3 ∨ p5) ∨ (p5 → False)) ∨ (True ∨ (False ∧ (((p5 ∧ p5) → (p3 → (p5 ∧ p1))) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50915249475686615739396278623 : ((((((p5 ∧ ((p2 → True) → p4)) ∨ ((p2 ∧ (p3 → True)) ∨ False)) → p4) → (p1 → p3)) ∧ ((((p3 → True) ∧ p4) ∨ p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



