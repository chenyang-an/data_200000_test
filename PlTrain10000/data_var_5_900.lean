variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321575270516751328787872655416 : (p4 ∨ (p2 → (p2 ∧ (p1 ∨ (((((p2 → (p2 ∨ (p5 → (p1 ∧ False)))) → (p3 → p2)) → True) ∧ (p5 ∨ ((p1 → True) → p1))) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58509858115620885039842166629 : (((p4 ∨ p5) ∧ ((p3 ∨ (p5 ∧ True)) → (((p5 ∨ (p3 ∨ (((p4 → p5) → (((p4 ∨ True) ∨ p2) ∧ False)) ∨ p2))) → p2) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157934387869718282552324730486 : ((((((p2 ∧ p2) ∧ p2) → p1) ∨ (p2 ∨ p4)) ∧ (p2 ∧ (p5 ∧ (((p5 ∧ p1) ∧ p3) ∧ False)))) ∨ (p5 → (p5 ∨ ((p3 ∨ p4) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241396713386069138060522411864 : ((False → p1) ∧ (((((p4 → True) ∨ p1) ∨ p1) ∧ (True ∧ ((((False → (p4 ∨ True)) ∧ False) → p5) → ((p5 → (p3 ∧ p2)) ∨ p5)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148564867284760163045151569857 : ((((True → False) → (p1 ∨ (True → (p3 ∨ (p4 ∨ p2))))) ∧ (((p1 ∧ ((p2 → p3) ∨ p3)) → p5) ∧ p2)) ∨ ((True ∨ (p1 → p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587446341638237679562274209368 : ((((((((True ∨ ((p5 → (((p2 ∧ False) → ((p4 → False) ∧ True)) → p3)) ∨ p1)) → (p2 ∨ p2)) ∧ (False ∨ True)) ∨ p4) ∨ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322444306184986176835141622934 : (p5 ∨ ((((True ∨ (p2 ∧ p5)) → p3) ∨ ((((p5 ∨ False) → p1) ∧ True) → ((((p3 ∨ (p4 → p2)) ∨ True) → p5) ∨ (False → p2)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148945468136062285838133550303 : (((p1 → (p2 ∧ (p3 ∧ p3))) → ((((p5 → True) ∧ False) ∨ p2) ∨ ((p4 ∧ p4) ∧ (p5 ∧ (p5 → p5))))) ∨ ((False → (p2 ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312031411278832171447673200314 : (p2 ∨ (p4 ∨ (p3 ∨ ((p3 ∧ ((False ∨ p5) ∧ (((True → (p3 ∧ ((False ∧ True) ∧ ((p3 ∧ p2) → p2)))) ∨ False) ∨ (p2 → p2)))) ∨ True)))) := by
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
theorem thm_5_vars_616328207645617199412916606517 : ((((((p4 → p3) ∧ (p1 ∨ (((p3 ∨ True) → p3) ∨ (True → False)))) ∨ ((((p4 ∧ (p3 ∨ p4)) ∨ (p5 ∧ p2)) → p5) ∨ p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727240669150076163091639843815 : ((((False ∧ (p1 → True)) ∨ ((p1 ∨ (p3 ∧ (True ∨ p3))) ∨ (((p1 ∨ p2) ∨ p1) ∨ ((p1 ∧ (p3 ∧ p5)) → ((p5 ∨ False) → p3))))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801187050690291580982060392684 : (((p2 → ((p4 ∧ (p5 ∨ (((((p3 ∧ (p5 ∧ (True → (True ∧ p3)))) ∧ False) ∧ p5) → p3) → p2))) → (p2 → (p2 → (False ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206488957882806707898747846014 : ((p5 ∨ (((p1 ∨ p4) ∨ p3) → p3)) ∨ (((True ∨ ((p5 ∨ ((((p5 ∨ p2) ∧ False) ∧ p2) ∧ (p5 ∨ p4))) ∧ False)) ∧ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323525457648906247618234115797 : (p5 ∨ ((p4 ∨ (((p3 ∧ True) ∧ (p1 ∧ (((True ∨ (p3 ∧ True)) ∨ p4) ∧ p5))) ∨ ((p2 ∧ (p2 → p1)) ∨ True))) ∨ ((p3 → p1) ∧ p3))) := by
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
theorem thm_5_vars_175153374262600173343207816448 : ((p5 ∧ (p5 ∨ (((p4 ∧ p5) ∨ ((p5 → p4) → ((p4 ∨ p4) ∧ p1))) ∧ p1))) → ((p2 ∧ p4) ∨ (((p3 → p4) → (p2 ∧ False)) ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684506921279798316070110786753 : (((((p3 ∧ (((p3 → p1) → p3) ∨ False)) ∨ (((p1 → (False ∧ p5)) → (p1 → p4)) ∨ p5)) ∨ (((False ∨ p2) ∨ p5) ∨ (p5 → p3))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52252756690969817456324873638 : (((p1 ∨ ((((p2 ∨ p3) ∨ p2) ∨ p5) ∧ (True ∧ (p2 ∨ ((p5 ∧ p4) ∨ True))))) → ((False ∧ True) ∧ ((p1 ∧ False) ∨ (p5 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586397079549056042115192666 : ((((p5 ∧ ((True ∧ ((p1 → p3) → False)) ∧ p1)) → (((p3 ∨ ((p5 → p1) ∧ p1)) ∧ p4) → ((p4 ∨ p5) → p5))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321685681614952882383620277427 : (p4 ∨ (p4 → (((p4 ∨ (True ∧ p5)) ∧ p1) → ((p3 ∧ p2) ∨ ((p4 ∨ (False ∨ p4)) → (((False ∨ p2) ∧ (p2 ∧ p1)) ∨ (p4 → p4))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113823263323330113660437667400 : (((p4 ∧ (p5 → (p4 → ((False ∨ p4) ∨ (p5 ∨ ((p5 ∧ ((p2 ∧ (False → (False ∧ True))) → p3)) ∧ True)))))) → (p1 ∧ p5)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260186984230775221640578351744 : ((p2 → p2) → ((((p4 ∨ (p4 ∨ p5)) ∧ p4) ∨ p4) ∨ (False → (((p2 → ((True → ((True ∨ (p3 ∧ p3)) → p3)) ∧ p3)) ∨ p4) ∧ p5)))) := by
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
theorem thm_5_vars_148252177179167775767840468362 : ((((p1 ∨ p5) ∨ ((p5 ∨ p2) ∧ (p1 → (True ∧ (p1 ∧ (p3 → (False ∨ False))))))) ∨ (False → (p1 ∧ p5))) ∨ ((p2 ∨ (p4 ∧ p1)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54423738069864959773928141870 : ((((((p2 ∧ p5) ∨ (p2 → True)) → p5) ∨ p5) ∨ (((p3 → (p2 → False)) ∨ p2) ∧ ((True → p3) ∧ ((p2 ∧ p3) → (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676166693211356727049248273597 : (((((((p3 → p4) ∨ True) ∨ False) → ((p2 ∧ (p1 ∧ (p4 ∧ p2))) → ((p4 → p3) ∨ (p5 → True)))) ∧ (p2 ∨ ((False ∨ True) ∨ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228691860153369089028201611797 : ((p2 ∨ (p2 ∨ p4)) ∨ ((((p2 ∧ p3) ∨ ((False ∧ (p4 ∨ True)) ∨ (p1 ∨ False))) ∨ ((p5 ∨ (True ∨ p3)) ∨ p2)) ∨ ((False → True) ∨ p2))) := by
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
theorem thm_5_vars_46943493778723697624071622390 : ((((p2 ∨ (p5 ∧ ((((p5 → False) ∨ ((False ∧ True) ∨ (True ∧ (False → p2)))) ∨ p2) → ((p1 ∧ True) ∧ p1)))) ∨ False) ∨ (False → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31792155993554149858914628498 : ((False ∨ ((p4 ∨ (False ∧ p3)) → (p3 → (((((p3 → (((p5 ∨ p1) ∨ False) ∧ p1)) ∧ (p1 → (p1 → p3))) ∨ p5) ∨ p3) ∧ True)))) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642211612322972928147026826564 : ((((True ∧ (p5 ∧ (((False → ((p1 ∨ (p5 ∧ (True ∧ ((p4 → p2) ∨ p1)))) ∨ True)) ∧ p1) → (((p1 → p3) ∨ False) ∧ False)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166446032732375569144276047727 : ((p2 ∨ (((p2 ∨ ((True ∨ ((p4 ∧ False) ∨ p3)) ∧ False)) → (True ∧ (True ∧ p4))) → p4)) ∨ (((False ∧ p2) ∧ True) → (p5 ∨ (True ∨ p4)))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689812097448516287631019589340 : (((((p1 ∨ p4) ∧ ((p3 ∧ (p1 ∧ (p3 ∧ p3))) → (False ∧ (p2 ∧ (p1 ∨ p3))))) ∨ ((((p3 ∧ p4) → p5) ∨ False) ∨ (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118347441795280160289541955053 : ((p2 ∨ ((((p1 → ((p4 ∨ (p3 ∨ ((((p5 → p5) → (p2 ∨ True)) ∧ (p1 ∧ p1)) ∧ p3))) ∧ True)) ∨ p2) ∨ p1) → p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50533835990221350628508986038 : (((((((((False ∨ p2) ∧ False) → (p5 → p4)) ∧ (True ∨ (p5 → True))) ∧ (p2 → False)) → p3) ∨ p4) → (p3 → ((True ∨ p2) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159170276634912034156406817205 : ((p1 → (((p5 → p3) ∧ ((p3 → (p1 ∧ p2)) ∨ p2)) → ((p5 ∨ ((True ∨ p2) ∨ True)) ∧ p5))) ∨ (False → (((p4 ∨ p4) ∧ p5) ∧ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47357724979544488392406870028 : ((((p5 ∧ False) ∨ (((p2 ∧ ((p5 ∨ ((p2 ∨ ((p3 ∨ p5) ∧ (p1 ∨ p2))) ∧ p2)) → p3)) ∧ (p3 ∧ p4)) ∨ False)) ∨ (False → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67860512536064131865872439017 : ((p2 → (((((True ∧ p3) ∨ (((True → p1) → False) → True)) → ((True → False) → p5)) → ((p1 → p2) → p3)) ∧ (p1 → (True ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107762383892581037436040882056 : (((True ∧ p4) ∨ (p2 ∨ ((False ∧ p5) ∨ (p2 ∨ ((True ∨ (False ∨ ((p4 ∨ False) ∧ (p2 → (p2 ∧ (p1 ∨ p3)))))) ∨ p5))))) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133701892668089782887261823594 : (((((((((p3 → False) → p2) ∨ p2) ∨ False) ∨ True) ∧ ((p5 ∧ True) ∨ True)) ∧ (((p5 → p4) → False) ∨ p4)) ∧ True) ∨ (p2 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764909951553940713909784532360 : (((p4 ∧ ((((True ∧ True) → (p2 ∧ p3)) ∧ ((False → (True → (True ∧ True))) ∨ (p3 ∨ ((False ∧ (p5 ∧ p1)) ∧ (False ∧ p3))))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205395007101067282782358414950 : ((((p5 ∧ p4) → p3) → (p4 ∨ False)) ∨ (p4 ∨ ((p4 ∧ (((True ∧ p5) ∧ p3) ∧ (p5 ∧ (p2 ∧ p2)))) → ((p1 ∧ True) ∨ (False → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199138934395932248010547027409 : ((((True → False) ∧ (p1 → (p3 ∧ p4))) ∧ True) → ((False ∨ (p4 ∧ p3)) ∧ (True → (True ∨ (p2 ∨ (p5 ∧ (((p3 ∧ p1) ∨ p3) → p5))))))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51387441342515546813124950801 : (((((True → p5) ∧ ((False ∧ (True ∧ (p4 → ((False ∨ p3) ∧ True)))) → (False → False))) ∨ p4) → (((p5 ∧ False) ∨ True) ∨ (p3 ∧ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37750074160920798010358776248 : (((((((p3 ∧ p5) → (p5 ∧ p2)) ∨ False) → ((p2 ∨ (False ∧ ((p4 ∨ False) → p4))) → (((False ∨ p2) ∧ p4) ∨ p2))) → p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137975424278633106206671930962 : ((p5 ∨ (((p5 ∨ (p4 ∧ (p3 ∧ True))) ∧ p1) ∧ (p1 → (p5 → ((p2 ∨ (p4 → ((p3 ∨ p1) → p4))) → p2))))) ∨ (p2 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330889551245095936367214979906 : (True → (p3 → (p5 ∨ (((p3 ∧ (p3 ∧ (p1 ∧ (((True → (p1 ∧ p2)) ∨ (True ∧ p3)) → (p4 ∧ (p2 ∧ p1)))))) ∨ (p4 ∨ p2)) ∨ True)))) := by
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
theorem thm_5_vars_146988731264733184486331741800 : ((((False ∨ ((((p2 ∧ (p4 ∨ p4)) → ((True ∧ p5) ∨ (True ∨ (p3 → p3)))) → p1) ∧ p2)) → p5) ∧ p4) ∨ (True ∧ (p2 ∨ (False → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142811955664450509247568481152 : ((p3 ∨ ((p1 ∧ p2) ∨ ((p1 ∧ (p5 ∨ ((True ∨ (((p1 → p1) ∧ p3) → False)) → (p2 ∨ (p1 → p3))))) ∨ p5))) → ((p3 ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678659003709889683511194335934 : (((((False ∧ p4) ∨ (p5 ∨ (p5 ∨ (p3 ∧ ((p4 ∨ ((False → p5) ∨ True)) ∧ ((p5 → True) ∨ p4)))))) ∨ ((p1 → p5) ∨ (p2 → True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_228831898344447712968885981281 : ((p3 ∨ (True → p3)) ∨ ((p4 ∨ False) → ((p5 ∧ (p3 ∧ p2)) ∨ (((p3 ∧ (p3 ∨ ((((False ∨ False) ∧ True) → True) → p4))) ∧ p4) → True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757388072943467110394484323242 : (((p1 ∧ ((p3 ∨ False) → ((((p4 ∨ ((p4 ∨ ((p4 ∨ p1) → True)) → p4)) → (True ∧ p2)) ∨ p4) ∧ ((p1 ∨ (True → False)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337385182419499262651105505305 : (p1 → ((False ∧ (p2 ∨ (((((p3 ∧ p5) ∧ (p3 → (p4 ∧ (False ∨ (False → p4))))) → p4) → p3) ∨ (p5 ∧ True)))) ∨ ((p4 → p3) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44597035788488521286687186336 : (((((p1 ∧ ((p2 ∨ p4) ∧ (True ∧ p2))) ∨ True) → ((((False → p2) ∧ p2) ∧ (((True ∧ True) ∨ p2) ∨ p3)) ∧ (False → True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149549688964549978926182463320 : ((p2 ∧ ((((p3 ∧ (p2 → False)) ∨ ((p2 ∨ (True → True)) ∧ (p2 → True))) ∨ p3) ∨ (p1 ∨ (True ∨ p1)))) ∨ ((p5 ∨ (p4 → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704135232114648826248097902876 : ((((((p3 ∨ p1) ∧ (p3 → (p5 → False))) ∧ (p3 ∧ p4)) → (p1 → (((p2 ∨ p2) → ((p2 ∨ p3) → (False ∧ (p4 → p4)))) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207302995347571054035990160562 : ((((p2 → (p2 ∨ p5)) → p4) ∨ p3) → (False ∨ (((p4 ∨ (((((p5 → p1) → False) → (p5 → p3)) ∧ p4) ∨ (p1 → p2))) ∨ p2) ∨ True))) := by
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
theorem thm_5_vars_321157620236067322069961437125 : (p4 ∨ (p2 ∨ (p5 ∨ ((((((True → p5) ∧ (False ∧ False)) ∧ (p2 → ((p5 ∧ (True ∨ False)) ∧ (p3 ∧ p5)))) → p3) → (False ∧ p3)) ∨ True)))) := by
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
theorem thm_5_vars_749129403261561289111625055834 : ((((p5 → p1) → ((p2 ∧ ((p4 → ((p1 ∧ ((p5 → (True ∧ p2)) → p5)) → p4)) → ((p4 ∧ p4) ∧ ((p3 ∧ True) ∧ True)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173898282491345241973067414922 : (((((p5 ∧ ((((p4 ∧ False) ∨ p3) ∧ (False → p5)) ∧ p5)) ∧ p3) → True) → False) → (False ∨ (p1 ∨ (((p2 ∨ True) → (p3 ∨ p3)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ ((((p4 ∧ False) ∨ p3) ∧ (False → p5)) ∧ p5)) ∧ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301964882487684619304166707782 : (False ∨ ((True → True) → ((p2 → (p4 ∨ p5)) → ((((False ∨ (((False ∨ (p3 → p3)) ∨ (p1 ∨ p3)) ∨ p4)) ∨ (p2 → p3)) → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661385892989072328565747783328 : (((((False ∧ (((p2 ∨ p4) ∧ p4) → (p4 ∧ (p4 → (((False ∧ (p2 ∨ (p3 ∨ p5))) ∨ p4) ∨ False))))) → (p4 ∧ True)) → (p5 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586136221765972449881643492410 : (((((((p2 ∧ ((True → (p4 ∧ True)) ∨ p5)) ∨ ((p2 ∧ (p2 ∨ p1)) → p1)) ∧ (p2 ∧ (p5 ∧ (p5 ∧ (p2 ∨ p3))))) ∧ p5) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326192732409074586090408565773 : (p5 ∨ (p2 → ((False ∨ p3) ∨ ((p3 → p3) ∧ ((((p4 ∨ (False ∨ p3)) ∨ (p4 → (p1 ∨ ((p2 ∧ (p3 → True)) ∨ True)))) ∨ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216490412462048049132801485525 : ((p5 → ((p3 ∨ p4) ∨ False)) ∨ (False ∨ ((((p3 ∧ (True ∧ (p2 → p5))) ∧ False) ∨ (p1 → p4)) ∨ (((False ∨ True) → (p4 ∧ p5)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135015187945365141771009636847 : (((p4 ∨ (p4 → ((p5 → ((False ∨ (p3 ∨ (p4 → p5))) → (((p4 ∧ p5) ∧ False) → p2))) → p5))) ∧ (False → p2)) ∨ (False → (p5 ∧ p2))) := by
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
theorem thm_5_vars_337543800529952501955023981240 : (p1 → (((p4 → (p5 → p2)) ∨ (((p3 ∧ ((True ∧ p2) → (p1 ∧ p3))) ∨ p1) → ((p2 → p2) → False))) ∨ (((False ∨ p3) ∨ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257051017266883271954793912732 : ((p2 ∨ True) → (True → ((False ∨ (p5 ∨ (p1 ∨ p2))) ∨ (((((False ∧ True) ∨ True) ∨ p1) ∨ (((p3 ∨ False) ∧ p1) ∨ p2)) ∧ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49021354092576860104911433485 : (((((((((p1 ∨ p2) → False) ∨ p2) ∨ (p1 ∨ (p3 → True))) ∨ True) ∧ ((p2 ∧ p1) ∨ (p1 ∧ p1))) → p3) ∨ (p2 ∨ (False ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_50227368167766553736947332029 : ((((p4 ∨ (((p2 → p1) ∧ (True ∨ p3)) ∧ (p1 ∧ ((True → p1) → ((True ∨ False) ∨ p3))))) ∨ p3) ∨ ((p2 → True) → (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41518371763549210244152934790 : (((((p5 ∨ (p4 ∧ (p3 → (p2 ∨ True)))) → (p4 ∧ p1)) ∧ (p2 → (p4 ∨ ((p1 ∨ (p3 → ((p4 ∨ p1) ∨ False))) ∧ p3)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157220893513057409028417827207 : ((((p1 ∨ ((False ∧ (True → (p5 ∨ (False ∨ (False ∧ p1))))) ∨ p3)) ∨ (p4 → (p4 → p3))) → p3) ∨ (p4 ∨ (True ∧ (p2 → (True ∨ True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47506242250282292318756231779 : (((p2 ∨ (((((p1 ∧ p2) ∨ (p4 → p5)) → (((((p5 ∨ p1) ∧ (p3 → p1)) → p2) ∧ p4) ∧ p4)) ∧ p3) ∨ False)) ∨ (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51474033353111588673821914829 : ((((((p1 ∨ True) ∨ (p3 ∨ (p5 ∧ p5))) ∧ p2) → ((p5 → p1) ∨ ((p3 ∨ p5) ∧ p5))) → (((p3 → False) → (p4 → p3)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357085587857656640637072643932 : (p5 → (((p5 ∧ p5) → p2) → ((((((p1 ∨ p2) ∨ (p4 ∨ ((p5 ∧ p5) ∧ p5))) → False) ∧ ((False ∧ False) → p1)) ∨ (True ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190828660558329909655701366177 : (((p5 ∨ (((p3 ∧ True) ∨ p3) ∨ p1)) ∨ (p3 ∧ p1)) ∨ (((p2 ∧ p1) ∨ ((((p2 → ((p5 → p5) ∧ False)) ∧ p4) ∧ p3) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4620783764708422674952585983 : (p4 → (p2 → ((p5 ∧ (p2 ∧ ((p5 ∧ ((((((p1 → p5) ∧ p2) → (p2 → (p2 ∨ p4))) ∨ False) → p1) ∧ p3)) ∧ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157236176928623098195337907832 : ((((p1 → (True ∧ (p5 ∨ (p2 ∨ ((True ∨ p1) ∧ p2))))) → ((p3 ∨ p3) → (p5 ∧ p5))) → p2) ∨ ((True → True) ∨ (p3 ∨ (False ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712021861156849698692492286990 : ((((((p3 ∧ p5) ∧ (p2 → p3)) ∨ p3) ∨ (p5 → (False ∧ ((p1 ∧ (p3 ∧ False)) → ((True ∧ p4) ∨ (p3 → ((False ∨ p2) ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338181869714399418715634886546 : (p1 → ((p3 → (((p3 ∨ False) ∨ False) → (p4 ∨ p4))) → (p3 → ((p1 ∨ p1) → ((((p5 ∧ ((p4 ∨ False) ∧ p3)) → p2) ∧ p2) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
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
theorem thm_5_vars_671545002679561171969249066373 : ((((p4 → ((p5 ∧ ((p1 → (p5 → True)) ∧ ((p5 ∧ (p3 → (p5 ∨ False))) ∨ False))) ∨ (p5 ∧ (p4 ∨ p4)))) ∨ ((p2 ∧ True) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53872911286326458461792912787 : ((((p1 ∧ False) ∨ ((p3 ∨ p2) ∧ ((p1 → p5) → p5))) ∨ (((False ∧ True) → (p4 → (False → p3))) ∨ (p2 ∨ (p4 ∨ (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171551655113766905542242052903 : ((((((((True ∨ p3) → p3) → (p4 ∧ p4)) → p2) ∨ (p4 ∧ p2)) → p5) ∨ p2) ∨ (p2 → (((True → True) → p4) → ((p3 ∨ False) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256578538747591637439170278271 : ((p1 ∨ True) → ((((True → (((p3 → (p3 ∧ p2)) → p5) → p4)) ∨ (False → (p1 ∨ p4))) → (((p3 → p5) ∨ (p2 → p3)) → False)) ∨ True)) := by
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
theorem thm_5_vars_303226514489476703265594444486 : (False ∨ (p5 → (((((p3 ∨ True) → (((True ∨ (p5 → False)) ∧ False) ∧ (p2 ∧ False))) ∨ p4) → ((p4 ∧ (p2 ∧ True)) ∧ (p4 ∧ True))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684950239928051076958402302564 : ((((p2 ∧ (p1 ∧ ((((p5 ∧ (p2 → p1)) ∧ p4) ∧ (p5 ∧ (p1 ∨ False))) ∨ (p4 ∨ p4)))) ∨ (p4 ∨ ((p5 → True) ∨ (False ∧ p4)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160076220680767200830055233872 : (((True ∨ (p3 ∨ (p4 → ((p4 ∨ True) → ((True ∨ ((True ∨ p2) ∧ p1)) → (True → False)))))) → p1) → ((p1 ∨ p4) ∨ ((False ∨ p4) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p3 ∨ (p4 → ((p4 ∨ True) → ((True ∨ ((True ∨ p2) ∧ p1)) → (True → False)))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640281580628230752176851334827 : (((((False ∨ (p4 → True)) → (((p5 ∧ ((p5 ∨ p5) ∨ p4)) ∧ False) → ((p1 → (((False ∧ True) ∧ p3) ∧ (p1 ∧ p3))) ∧ p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257975844832169385386694302458 : ((p4 ∨ p1) → (((False ∨ (((p1 → False) ∧ p2) ∧ p3)) ∨ (((p3 ∧ (p4 ∨ p1)) → (True ∨ (p3 → (p4 ∧ (p5 → p2))))) → False)) ∨ True)) := by
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
theorem thm_5_vars_408648872821360533884604769547 : ((((((False → p3) → ((((p4 ∧ p5) ∧ False) ∧ (p3 ∨ (False ∨ True))) ∨ (False → (p1 → (p5 ∨ p5))))) → ((p4 ∧ p3) ∧ False)) → p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p3) → ((((p4 ∧ p5) ∧ False) ∧ (p3 ∨ (False ∨ True))) ∨ (False → (p1 → (p5 ∨ p5))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309036338888242590547389995379 : (p2 ∨ (((p4 → False) ∧ ((((p4 ∧ p2) ∨ (p1 → (p3 ∨ (((p4 ∨ True) ∨ p5) ∨ True)))) ∨ (((p4 ∨ False) → p4) ∨ p1)) → False)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∧ p2) ∨ (p1 → (p3 ∨ (((p4 ∨ True) ∨ p5) ∨ True)))) ∨ (((p4 ∨ False) → p4) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57840028873234609241368696596 : (((p5 ∧ (p1 ∨ p4)) → (p2 ∧ (((((p4 ∧ p4) ∧ p2) ∧ ((True ∧ p5) ∨ (p3 ∨ (True ∨ p3)))) ∨ ((p3 ∨ p5) → p2)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313242911375858726129385838201 : (p3 ∨ (((True → p3) ∨ ((p3 ∧ ((p5 ∨ (((p4 → True) ∨ False) → (True → (p1 → p2)))) ∧ (p3 ∨ p2))) ∧ (False → (p2 ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684730619554704463348369728981 : (((((p4 ∨ p1) ∧ (True ∨ (p2 ∧ (((p1 → p2) ∧ (False ∨ ((p5 → False) ∧ p4))) ∧ p4)))) ∨ ((p1 → ((p4 → p5) ∨ p5)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158367275326420144104450069354 : (((p3 ∨ p1) ∧ ((False ∨ (((p2 ∧ (p2 ∨ ((True ∨ p4) → (True ∧ False)))) ∨ p2) ∧ p2)) ∧ p3)) ∨ ((p2 ∨ True) ∨ ((p3 ∨ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741154907980193222359147841334 : ((((p4 ∨ p1) ∨ (((p2 → (p5 ∨ p1)) ∨ (p5 ∨ (p3 ∨ ((p3 ∧ p4) ∧ p3)))) ∨ (p3 ∨ ((p3 → (p3 ∨ (p5 → False))) ∨ p4)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62298646735437477153582706346 : ((p3 ∧ (((((((p1 ∧ (p5 → (False → (p5 ∧ True)))) → False) → False) ∧ ((p3 ∧ p4) → (p2 ∧ p4))) ∨ p4) ∧ p1) ∧ (p3 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140761049246350623146149465750 : (((p4 ∧ (((False ∧ p5) ∨ (p2 → False)) → (False ∧ ((p5 → True) ∨ False)))) → ((p5 → p2) ∧ ((p2 ∧ p3) ∧ p4))) → (p3 ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62670581172678884922263612733 : ((p4 ∧ (((p1 ∨ p1) ∧ (p2 → (((p5 ∧ (((p2 → False) ∨ p2) → False)) ∧ ((True → (False → p2)) ∨ False)) → (False ∧ True)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693770582232541544264843571563 : (((((((((p3 ∧ p1) → p4) ∨ (p1 → (p4 ∧ p4))) ∨ p1) ∨ False) → p3) ∨ (p5 ∨ ((p3 ∧ p4) → ((True ∨ (p1 ∧ p5)) → True)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158655497289669302703193147511 : ((p1 ∧ (True ∧ (p3 ∨ ((p5 ∧ ((((p3 ∧ (p3 → False)) ∧ False) ∧ (p4 ∧ True)) ∨ p1)) ∨ False)))) ∨ ((p2 ∧ ((True ∨ p1) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183964211817496346484722254427 : (((p1 → (p1 ∧ (((p2 ∨ p2) ∨ (p4 ∨ p2)) ∨ p3))) ∧ p1) ∨ ((False ∧ (p5 ∧ ((p3 ∧ p2) ∨ p4))) → (True ∧ (False → (p1 → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190726621115630036168534942566 : ((((False ∨ p2) ∧ (p5 ∨ (p1 ∧ True))) ∧ (p5 ∨ p2)) ∨ (p3 → (((p2 ∧ (((False ∧ False) ∧ False) ∨ p3)) → p1) → ((p2 ∧ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



