variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350163577075886453858184937701 : (p4 → ((((True → (p3 ∨ ((p2 → False) → False))) → p1) → (p4 → ((p2 → p1) ∧ (p4 → ((p4 → True) → (p1 → (p1 ∧ p3))))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215386289008068046397906651125 : ((p2 ∧ (p1 ∧ (p5 ∨ p3))) ∨ (False ∨ (True ∨ (((((p3 → p1) → (((p4 → True) ∨ (p1 ∨ p2)) ∧ p4)) ∨ (True ∧ p4)) → p4) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113992024980398267645336714383 : (((p1 → (((p5 → p2) → (((p1 ∨ p2) ∧ (p3 ∧ ((p1 ∨ (True ∨ False)) ∨ p3))) ∧ p4)) ∧ p2)) ∧ ((False ∨ p2) ∨ p2)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637433248713066842324533774249 : ((((((False ∨ ((p4 ∨ p2) ∨ p5)) → ((p2 → p1) ∨ p1)) ∧ (p2 → (p5 → (p3 ∧ (((p2 → (p3 ∨ False)) ∨ p5) ∨ p4))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50547596674947171201233157830 : (((((True ∨ p4) ∨ (p2 ∧ (((True ∨ (False ∧ p5)) ∧ p2) → (((False → False) ∧ p4) ∨ False)))) ∨ p4) → (((p1 ∨ False) ∨ p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63073861823726682087549804596 : ((p5 ∧ ((((((p4 ∨ (p3 → p4)) → True) ∧ (((False → True) ∧ ((p1 → p3) → p5)) ∨ (False ∧ (p1 ∨ True)))) ∧ p3) ∨ p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136541134998683216648810397274 : ((((p2 ∧ p4) ∧ False) ∨ (False ∨ ((p3 ∨ (False ∧ p3)) → (p4 → (((p5 ∧ p5) → p2) ∨ (True ∨ (p4 ∧ p5))))))) ∨ (p5 ∨ (p4 ∧ False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672322119383076582281126926794 : (((((((((((True ∨ ((True → False) ∧ p2)) ∨ p1) ∧ p1) ∨ p3) → (True ∨ False)) ∨ p1) ∨ (False → p5)) → True) → (p1 ∧ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57802132889943308611794829417 : (((p2 ∧ (True ∧ p3)) → (((((True ∧ p5) ∨ (p2 ∨ ((p3 ∨ p5) ∧ p1))) → ((False ∨ (p4 ∧ False)) ∨ p2)) ∧ p3) ∨ (p5 → True))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8744356783570827719707599304 : (((((p3 ∨ (False ∨ p5)) ∧ (((p2 ∧ ((p3 ∧ p2) ∨ ((p1 ∧ p1) ∧ True))) ∧ (p4 ∨ True)) ∨ False)) ∧ (False ∨ (p4 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206501488289753487365460145639 : ((p5 ∨ ((p2 ∨ p4) → (p4 ∧ p2))) ∨ (((p5 → p5) → (p2 → p1)) → ((p4 ∧ (((p5 → False) → p4) ∨ p1)) ∨ ((p2 ∧ p5) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725669563344770315878656185458 : (((((True ∨ False) ∧ p1) ∨ (p5 → (((((p1 ∧ (p2 ∧ False)) → p4) → (p4 ∨ False)) → (False ∨ p2)) ∨ (False ∧ ((False ∧ p3) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113910476162824105784365752756 : ((((p3 ∨ (((p2 → p3) ∧ ((((False ∧ False) ∨ False) ∨ p3) → (False → p3))) → p2)) ∧ (False ∧ p5)) ∧ ((p2 ∨ True) ∨ p4)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431987481852390202448976155274 : ((((p2 ∨ (((((p1 ∧ True) ∨ p3) ∧ (p5 ∧ ((True → True) → (p3 → (p5 ∧ p3))))) ∧ (True → (False → p1))) → p4)) ∨ (p5 → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64020314385418770592437405504 : ((False ∨ ((p1 → (((p2 → (p5 ∨ (p4 → False))) ∨ p3) ∧ ((((p1 ∧ p4) ∨ ((p4 ∧ p4) → False)) → p4) ∧ p1))) ∨ (p3 → p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781448144543267105221340128364 : (((p2 ∨ (p4 ∧ ((((False ∧ p2) → p3) ∧ (True ∨ False)) ∧ ((p4 ∧ (((((p4 → p4) → False) ∨ False) ∧ (p3 ∧ p1)) → p3)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159448411438947312834405358252 : (((((p5 ∧ False) ∨ (p5 → (p5 ∧ (((p4 ∨ p3) ∨ p2) ∨ p4)))) → ((p1 → True) ∧ p4)) ∧ p2) → ((p2 → True) ∧ (p4 ∧ (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 ∧ False) ∨ (p5 → (p5 ∧ (((p4 ∨ p3) ∨ p2) ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660086680385571578460969382343 : (((((((False ∧ (p1 ∨ ((p5 → p5) → (((False ∨ (p2 → p5)) ∨ p4) → p3)))) → True) ∧ ((False ∨ p5) ∨ p2)) ∨ True) → (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704178282623575215138557293111 : ((((((p4 → (True ∨ (p5 → p1))) → p3) ∨ (True ∧ p3)) → (((p5 ∧ p3) ∨ True) → ((((True ∨ (p5 → p5)) → False) ∨ p3) ∨ p4))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p4 → (True ∨ (p5 → p1))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144756032459886629205285821664 : ((((((((p3 ∧ True) → p3) ∨ ((False ∧ False) ∨ p3)) ∨ (p4 ∧ p1)) ∨ p2) → p2) ∨ ((False ∧ p2) ∨ True)) ∧ (True ∨ ((p3 ∧ p4) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242327252599032537435609247886 : ((p2 → p2) ∧ ((((p1 ∨ (p1 → p3)) → (p1 ∧ True)) → ((p4 ∧ (p3 ∨ False)) → False)) ∨ ((p2 ∨ ((False ∨ (p3 ∨ True)) → p4)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255628461940364188230673509236 : ((p5 ∧ p4) → (((p2 → True) → (((((True ∨ False) ∧ False) ∨ p1) ∧ p5) ∨ p1)) ∨ (True ∨ ((((True ∨ (p5 → p2)) → p4) ∧ True) ∨ p5)))) := by
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
theorem thm_5_vars_156840191887617954475835792020 : (((p2 → ((((((True ∨ False) → p2) ∨ p5) ∧ (p2 ∨ p3)) ∧ p2) → ((p5 ∧ p1) ∨ True))) ∧ p3) ∨ ((p1 → p5) → ((p2 ∧ p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_627566632471522746267792560635 : (((((((True ∨ (p2 ∨ p1)) ∧ ((p4 ∨ (((p2 ∨ p4) ∨ p2) ∨ ((False ∧ p5) ∨ (p2 ∨ True)))) → p3)) ∨ (False ∧ p3)) ∧ p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668747130511400931505806910654 : (((((((p3 ∨ (p5 ∧ (((True → True) ∧ (((p2 ∨ False) → p3) ∨ p1)) → p5))) ∧ (False ∨ p4)) → p2) ∨ p2) ∨ (p5 ∧ (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136114322674865275007410005709 : ((((False → p1) → (p3 ∧ (False ∨ (p1 ∨ p4)))) ∨ (((((False ∨ p1) → False) → p5) → p1) ∧ ((p2 → p4) ∨ False))) ∨ ((True → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318558807955575202779317539498 : (p4 ∨ (((((False ∧ p3) ∨ (p3 ∧ p3)) ∧ (((False ∨ False) → ((((p4 ∧ False) ∧ (p3 ∧ p3)) ∧ True) ∧ p1)) ∨ True)) ∨ p3) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45789786781484229623660153479 : (((p1 → (((((False ∧ p5) ∧ p3) ∧ (p4 → ((p1 ∧ p4) → ((p4 → False) ∧ (p5 ∧ p4))))) ∧ (p4 ∧ p4)) → (p3 ∧ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255673095501573787447829253992 : ((p5 ∧ p5) → ((((((p1 → (p4 ∧ (p5 → p2))) ∧ (p2 → p1)) ∧ (p5 ∨ p3)) ∧ p1) ∧ ((p1 ∨ True) ∨ ((False ∧ p2) → True))) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h1.left
        let h15 := h1.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h17 := h9 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h25 := h9 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h1.left
      let h31 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h32 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h33 := h9 h32
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h35 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h36 := h34 h35
      -- One of the premise coincides with the conclusion.
      exact h36
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h1.left
        let h41 := h1.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h42 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h43 := h9 h42
        -- We need to get the right conjuct of h43 based on <expert-advice>.
        let h44 := h43.right
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h45 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h46 := h44 h45
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h47 =>
        -- Conjunctions on the left can always be decomposed.
        let h48 := h1.left
        let h49 := h1.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h50 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h51 := h9 h50
        -- We need to get the right conjuct of h51 based on <expert-advice>.
        let h52 := h51.right
        -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
        have h53 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h49
        -- We have shown the premise of h52, we can now drive its conclusion.
        let h54 := h52 h53
        -- One of the premise coincides with the conclusion.
        exact h54
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h1.left
      let h57 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h58 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h59 := h9 h58
      -- We need to get the right conjuct of h59 based on <expert-advice>.
      let h60 := h59.right
      -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
      have h61 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h57
      -- We have shown the premise of h60, we can now drive its conclusion.
      let h62 := h60 h61
      -- One of the premise coincides with the conclusion.
      exact h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809218841186406341645417207451 : (((p5 → ((((((p3 → ((True ∧ False) → p3)) ∧ ((p2 ∨ False) → p4)) ∨ p1) → ((p4 → p4) ∧ p4)) ∨ ((True ∧ p5) ∨ p3)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_60839343523223283260371660224 : ((True ∧ (p1 ∨ ((((((p3 ∨ p4) ∨ (True ∧ ((p4 ∨ p3) ∨ ((False → (True ∧ p3)) ∧ p1)))) ∨ True) ∨ p4) ∧ True) ∨ (p1 → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_608876603601377423287594520202 : (((((((((p5 → (p2 ∧ False)) ∨ p3) ∨ True) → (p4 → (p5 → ((p3 ∧ True) → p5)))) → (((p5 → False) ∧ p1) ∧ p4)) ∨ True) ∨ p4) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_313945162918496065690189471085 : (p3 ∨ (((((((True ∨ p5) → (p3 → (p5 → p1))) ∨ (True → p4)) ∨ (p3 ∨ p4)) ∧ ((True ∨ (p5 → p1)) → True)) → p3) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45985887172560171683041663895 : (((((p1 ∧ (((((p4 ∨ True) ∧ p4) ∧ (p2 ∨ p5)) ∨ (p3 ∧ p1)) → (p2 ∨ (True ∧ (p1 ∧ True))))) ∨ p1) ∧ p1) ∧ (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777352984371336321418469630939 : (((p1 ∨ ((p5 ∨ (((p5 ∧ (p4 ∧ (p4 ∧ p5))) → (((p1 ∨ p2) ∨ (p1 ∧ True)) ∨ p5)) ∨ p1)) ∨ (p2 → ((p3 ∧ True) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60238070549751010415096451539 : (((True → p4) → (p4 → ((((p4 ∧ (False → ((p2 ∧ p2) ∨ (True ∧ False)))) ∨ (False ∨ (p5 ∧ p5))) ∧ (p2 → p2)) → (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47148190611585300845435216131 : ((((((p3 → True) → p4) ∧ ((((p5 → (p5 ∧ (p2 ∨ p5))) ∧ False) ∨ p3) ∧ p1)) ∨ (p5 ∧ ((p5 → p1) ∧ p4))) ∨ (False → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42556638285900857082034469175 : (((p1 ∨ (p5 ∧ (((((p3 ∧ (p4 → (True ∨ (p5 → (False ∨ p2))))) ∨ ((True ∨ (False ∨ p2)) ∧ p1)) → p4) → p2) ∨ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150565995608118310990301970608 : ((((True ∧ (p5 → p5)) ∧ ((((p2 ∧ False) ∨ p4) → p5) ∧ ((p5 ∨ (p1 ∨ (p3 → p1))) ∧ p4))) ∧ p4) → (p2 → ((False ∨ p5) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h17 : ((p2 ∧ False) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679472717680493076529362643316 : ((((((p2 ∨ (((((False ∧ True) ∧ (False ∨ p3)) → (p3 ∧ p4)) ∨ False) ∨ (p1 → p2))) ∨ p2) ∧ p1) → ((p3 ∧ (p1 ∨ p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63428090612068385326774585774 : ((p5 ∧ (p1 → ((p4 ∨ (((((p4 → ((p4 ∧ p5) ∧ p4)) ∧ (p3 → (p3 → p1))) → p5) → (p1 ∧ (p3 ∨ False))) → p2)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134968510983032197429759360889 : ((((p2 ∨ (((True ∧ p5) ∨ False) ∨ p2)) ∨ (p4 ∨ ((p2 → ((False ∨ p3) → (p5 → p5))) → p2))) ∧ (p4 ∨ p2)) ∨ (p5 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128141060059071315393954252603 : ((p2 → ((p2 ∧ ((False ∨ False) → ((True → False) ∧ p5))) → (p5 ∨ ((p1 → ((((p5 ∧ p2) ∧ p5) → p3) ∧ p3)) ∧ p4)))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58539710767722899299813302088 : (((p5 ∨ p3) ∧ (p1 → (p3 → (p1 → ((p1 → ((p4 ∨ p3) ∨ p2)) → ((p2 ∧ p4) ∧ (((False → p5) → p5) ∧ (p2 ∧ True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184485662970999039259533097243 : ((((p2 ∨ (((p4 → True) ∨ True) ∧ p2)) → p3) ∨ (True ∧ p2)) ∨ ((((p1 → False) → (False ∨ (p3 ∧ p3))) ∨ True) ∨ (True ∧ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356256272627157756390079016350 : (p5 → ((((p4 ∨ ((p1 ∧ p2) ∧ p2)) ∨ (p3 → ((p1 → False) ∨ True))) ∨ (p3 ∧ p3)) ∨ (((p2 → (p1 → p4)) ∧ (p1 → p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_244598858321423039282044991250 : ((False ∧ p4) ∨ (p3 ∨ (((True → (((p5 → (False ∧ (True ∨ ((p1 ∧ p1) → p2)))) → p1) ∧ (p4 ∧ False))) → p3) ∨ ((p3 ∧ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299996607125610683542030281267 : (False ∨ (((p5 ∨ ((True ∧ False) ∨ (False ∧ p1))) ∨ (((p3 ∧ (p2 ∧ p5)) ∨ ((False ∨ p2) ∨ (True → p3))) → (False → p4))) ∧ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166339485762329369098925706512 : ((p5 ∧ (p2 → (p3 → ((p5 ∨ ((p4 ∨ True) ∧ (p2 → (p5 ∧ (p2 ∨ True))))) ∨ False)))) ∨ (True ∧ (((p4 → p5) ∨ (True ∨ p2)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226977076486528379172782023348 : (((False ∨ p5) → p4) ∨ ((p1 → False) → (p4 → (p2 → (False ∨ ((p2 ∨ (False → p3)) ∧ (p5 ∨ ((((p1 ∨ p4) ∨ False) ∧ p1) → False)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721810719668277085212921611350 : ((((p3 ∨ ((True ∨ p5) ∧ p2)) → (((p5 ∧ (p2 ∧ (False ∧ ((p1 ∨ p4) → p3)))) ∨ ((p5 ∨ True) → (p2 ∧ (True ∧ False)))) → p4)) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
    cases h1
    case inl h11 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h20 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h21 := h10 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h25 : (p5 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h26 := h10 h25
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- False on the left can always be used.
        apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50909733227333565606913315858 : ((((((p4 → False) ∧ (p4 ∨ True)) ∧ (p5 ∨ (p1 ∨ ((p3 ∧ p1) ∧ p2)))) ∨ (p3 ∧ p4)) ∧ ((p4 ∧ (p3 → (p5 ∧ p3))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615162750715648474168934912843 : (((((((p3 ∨ ((p4 ∧ (p1 ∨ (False → p4))) ∧ True)) ∨ p2) ∨ (p2 ∧ (p5 ∧ True))) ∧ (p1 → (p5 ∧ ((p1 → True) ∨ p5)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68977168633192449370163696123 : ((p4 → (p5 → ((((p1 → (p4 ∧ (p1 → (False ∨ ((p1 → p2) ∧ False))))) ∨ (((True ∧ p5) → (False ∨ p3)) → p4)) → p3) ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_180284417707125668497747950468 : (((p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) → False) → ((p3 ∨ (p5 ∧ (p2 ∨ p3))) ∧ ((False ∧ (p3 ∧ p1)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
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
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h20.left
    let h28 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h29 := h1 h16
  -- False on the left can always be used.
  apply False.elim h29
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h30 : (p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h31
    -- Implications on the right can always be decomposed.
    intro h32
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- Conjunctions on the left can always be decomposed.
    let h41 := h34.left
    let h42 := h34.right
    -- One of the premise coincides with the conclusion.
    exact h31
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h43 := h1 h30
  -- False on the left can always be used.
  apply False.elim h43
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h44 : (p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h45
    -- Implications on the right can always be decomposed.
    intro h46
    -- Conjunctions on the left can always be decomposed.
    let h47 := h46.left
    let h48 := h46.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h47.left
    let h50 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h49.left
    let h52 := h49.right
    -- Conjunctions on the left can always be decomposed.
    let h53 := h52.left
    let h54 := h52.right
    -- Conjunctions on the left can always be decomposed.
    let h55 := h48.left
    let h56 := h48.right
    -- One of the premise coincides with the conclusion.
    exact h45
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h57 := h1 h44
  -- False on the left can always be used.
  apply False.elim h57
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h58 : (p5 → ((((p1 ∧ (p2 ∧ True)) ∧ p2) ∧ (True ∧ p3)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h59
    -- Implications on the right can always be decomposed.
    intro h60
    -- Conjunctions on the left can always be decomposed.
    let h61 := h60.left
    let h62 := h60.right
    -- Conjunctions on the left can always be decomposed.
    let h63 := h61.left
    let h64 := h61.right
    -- Conjunctions on the left can always be decomposed.
    let h65 := h63.left
    let h66 := h63.right
    -- Conjunctions on the left can always be decomposed.
    let h67 := h66.left
    let h68 := h66.right
    -- Conjunctions on the left can always be decomposed.
    let h69 := h62.left
    let h70 := h62.right
    -- One of the premise coincides with the conclusion.
    exact h59
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h71 := h1 h58
  -- False on the left can always be used.
  apply False.elim h71



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309332931844845666601900559611 : (p2 ∨ ((((p5 ∨ ((p5 ∧ p3) ∧ ((p1 → (False ∧ ((p3 → p4) ∨ p4))) ∨ p2))) ∨ ((p1 → p4) ∧ True)) ∨ (p1 ∧ p3)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620167813406056584061985298770 : (((((p2 ∧ p2) ∨ (((((True ∨ ((False ∧ p2) → (p5 → p1))) ∨ (((True ∧ p4) → p2) ∨ p3)) ∧ (p5 → p2)) → False) ∨ p5)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_1483990717644303281088312532 : ((((False → (p1 → p3)) → ((((((p1 → p3) ∨ (p3 → True)) ∨ (p3 ∨ p3)) ∧ p5) → (p5 ∧ p4)) → p2)) → p1) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603547293555291602865762498861 : ((((p3 ∨ ((p2 ∨ False) ∨ (p1 → ((True → ((p3 ∧ ((p2 → p1) ∧ p4)) → (((False ∧ True) ∨ (p2 → True)) ∧ p2))) ∧ p3)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594596441290668954926671871674 : (((((p5 ∨ ((p4 → p2) → ((((True ∧ True) ∨ (True ∨ p3)) ∧ False) ∧ (p1 ∨ p1)))) ∨ (False ∨ (p4 ∨ (False → (p2 ∨ False))))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626562981446473080262282276170 : ((((p4 → (((False ∨ p1) ∧ True) ∨ (((((p5 ∨ True) ∨ False) ∧ (p5 ∨ False)) → p5) → (p4 → ((p3 → p2) ∨ (p4 ∨ p3)))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_158661719411957023904923664206 : ((p1 ∧ (p4 ∨ (p1 → ((p3 ∨ p2) ∨ ((p5 ∧ p3) ∧ ((True ∨ (p2 → p1)) ∧ (p1 ∨ False))))))) ∨ (((False → (p4 → p2)) ∧ True) ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194233228951712658828120276533 : ((p4 → (((p5 ∧ ((p5 ∧ p4) ∨ False)) ∨ p2) → False)) → ((((p2 ∨ False) ∨ (p2 ∧ False)) ∧ (p4 ∧ True)) ∨ (((p3 → p2) ∧ p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313974676568552352561655795622 : (p3 ∨ (((((p2 ∧ (p3 → p3)) ∧ (False → (False → True))) → (p3 → False)) ∨ ((False → (p1 ∧ (False ∧ True))) ∨ (True ∧ p1))) ∨ (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119197962790986039563943771011 : ((p2 → (((p4 ∧ False) → ((((p1 ∧ True) ∧ False) ∨ p1) → (((True ∨ (p1 ∧ p3)) ∨ p3) → False))) → (p2 → (p1 ∨ False)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_423658675141674323457910865537 : (((((((p1 ∨ (p4 ∨ (p2 ∨ False))) ∨ (((p5 ∨ (p2 → p4)) → p4) → False)) ∨ False) ∨ (((True ∧ False) ∧ True) → p4)) ∧ (True ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59619717644615021589280406703 : (((p5 → False) ∨ ((((False ∨ (p2 → (((False ∨ False) ∨ (p3 ∧ p5)) → ((p4 ∨ (False ∨ p2)) ∧ p2)))) ∨ (False ∨ p2)) ∨ True) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115968903351082401974840826624 : (((((p1 → p5) → p2) ∧ p4) → ((p2 → (p4 ∧ ((p1 → p2) → (p3 ∨ ((((p1 ∨ p5) ∨ False) ∧ p3) ∨ False))))) ∨ True)) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_300872876590028333474705948728 : (False ∨ ((((((p2 → (p5 ∨ True)) ∨ p5) ∨ (p1 ∧ p2)) → False) ∧ (p2 ∧ p1)) ∨ (((True ∨ p2) → ((p2 ∨ (p5 → p3)) ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702396244102385358685026057596 : ((((((p4 → (p1 ∨ (False → p4))) → (p3 ∨ p3)) ∨ True) ∨ (((p3 ∧ p5) → (True ∧ (p1 ∨ ((p3 ∧ (True → p1)) ∧ p2)))) ∧ p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_113804392339018248959712633691 : ((((p5 → p1) → ((p4 ∨ p3) ∨ (p3 ∨ (True ∧ (((True ∨ (p2 → False)) ∨ p1) ∧ ((p1 ∧ p5) ∨ False)))))) → (p2 → False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777552570289505629035238007949 : (((p1 ∨ (((False ∧ ((((False ∧ p2) ∧ p3) ∨ (p3 → p4)) ∧ p4)) ∧ p2) ∨ ((((True ∨ (p3 ∧ True)) ∨ p3) → p1) → (False → False)))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41392986115203238766534172933 : ((((((p5 ∧ True) → p5) → (p1 ∨ ((True ∨ (p3 ∨ (True ∨ p5))) ∧ p2))) ∧ ((((True ∧ (p4 → p2)) → False) ∧ False) ∨ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59008507739470518808811004576 : (((p3 ∧ p3) ∨ ((((False ∧ False) → (((p3 → ((p5 ∧ (False ∨ (p2 ∨ True))) ∨ p2)) → p1) ∨ False)) → (p2 ∨ p1)) ∨ (True ∨ p3))) ∨ p5) := by
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
theorem thm_5_vars_504455846340101514274209442432 : ((((False ∨ (p5 ∧ p1)) → (((p4 ∧ p1) ∨ (((((((False → p2) → p3) → p1) ∨ (p5 → p1)) ∧ p5) ∧ p5) → p4)) ∨ (p4 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_154739260067721893799618209808 : (((((((True ∧ p4) ∨ p2) ∧ (False ∨ False)) ∨ p1) ∨ (True → (p5 ∨ (True ∧ True)))) ∨ (p2 → p3)) ∧ ((True ∨ ((p2 ∧ p1) ∧ False)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327815898340592738290302175752 : (True → ((((((p2 ∧ p3) ∧ p5) → False) ∧ (True ∧ ((p5 ∨ (False ∨ (p4 ∨ True))) ∨ ((p5 ∨ p1) → (p1 ∨ p1))))) → p4) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49799925263421366966224890920 : (((True → ((((p1 ∨ ((False ∨ p4) ∧ p3)) ∨ p2) ∨ (((True ∧ p5) ∨ p1) ∧ (p4 ∧ p2))) ∧ (False → p1))) → ((False → p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763484660663935991467834983045 : (((p3 ∧ (p1 ∧ (p2 ∧ (p1 ∨ ((True ∧ (p4 ∨ (((p2 ∧ p2) ∧ (True ∨ (p1 → p1))) → p5))) ∨ (p2 → (p2 ∧ (p1 ∨ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193787010185332445888338760292 : ((p4 ∧ (((p3 ∨ p3) → p4) ∨ (p5 ∨ (p4 ∨ p1)))) → (False ∨ ((p5 ∨ p4) ∨ ((False ∧ ((p4 ∧ p3) ∧ ((p5 → True) ∨ p4))) ∧ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55991054637058709548240320278 : ((((p3 ∨ (False ∨ p1)) ∧ p3) ∨ ((p4 → ((p2 ∨ True) ∧ (p2 ∧ ((p3 ∧ False) ∧ (p2 ∧ (p2 → p3)))))) ∧ (p5 → (p1 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317615897796174510966508469030 : (p4 ∨ ((((p4 ∨ ((p5 ∧ (p4 ∧ (p5 → (p5 ∧ ((p2 → (((p4 ∧ p5) → False) → p4)) → (False ∨ True)))))) ∧ p3)) ∧ False) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620247402745641397785679784968 : (((((p5 ∧ p2) ∨ (p3 ∧ (((p3 ∧ True) ∧ p5) ∧ (((((p3 ∨ False) ∧ (False ∧ p3)) ∧ (False ∨ p4)) → p5) ∨ (p4 → p3))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149572963942639904680249169471 : ((p2 ∧ (p4 ∨ ((False → (False ∨ (p2 ∧ p4))) → (p1 ∧ (p4 ∧ (((True ∨ p3) → p2) ∧ (p2 ∨ p2))))))) ∨ (False ∨ (p5 → (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138404882438609114881690222655 : ((p5 → ((((p4 → (False → ((p2 ∨ ((True ∧ p1) → False)) → p4))) ∨ (p1 → (p5 ∨ (p1 → p5)))) → p3) ∧ p5)) ∨ (p5 → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135269425384819967486667618080 : (((False ∨ (True ∨ (p5 ∨ ((p1 ∧ False) → ((p3 ∧ ((p4 ∨ p1) → (p4 ∨ (False ∨ p4)))) ∨ False))))) → (p5 ∨ p3)) ∨ (p2 → (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148322978992930862293863123752 : (((p3 → (p1 ∨ (p4 ∨ ((p5 → (p4 ∧ p2)) ∧ (((True ∨ p1) ∧ True) ∧ False))))) → (False ∧ (p1 → p3))) ∨ (False → (True ∨ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314050888836448522455264066392 : (p3 ∨ (((((p4 ∨ ((p2 → (False → (p3 → (p1 ∧ p2)))) ∨ (p5 → (False ∨ p1)))) → (p2 ∧ False)) ∧ (p1 ∧ p5)) ∨ False) → (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ ((p2 → (False → (p3 → (p1 ∧ p2)))) ∨ (p5 → (False ∨ p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h7
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h19 : (p4 ∨ ((p2 → (False → (p3 → (p1 ∧ p2)))) ∨ (p5 → (False ∨ p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h21
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h23 := h15 h19
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151714064956280345769718577179 : ((((p3 → (p5 ∨ ((p4 ∨ (p5 → p1)) ∧ p4))) → (p5 ∨ ((True → p3) → p2))) ∨ ((p3 ∨ p2) ∨ False)) → ((p2 ∧ (p1 ∨ True)) ∨ True)) := by
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
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57692152881587509054125951665 : ((((True ∧ False) → True) → ((p4 ∨ ((p1 ∨ ((False → p3) → ((p3 ∧ (p5 ∨ p3)) → p4))) ∧ p5)) ∧ (p4 ∨ (p3 → (p4 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45753626674840954279497258185 : (((False → (((p2 ∧ True) ∧ (p4 → (((False ∨ ((True ∨ p1) ∨ (True ∨ p1))) → p3) ∧ p2))) ∨ (p3 ∨ (p5 → (p4 ∨ True))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166536775251678421965103923239 : ((p5 ∨ ((((((p4 ∨ p2) ∧ p4) ∨ ((p3 ∧ p1) ∨ True)) ∧ True) → (p2 ∨ True)) ∧ p4)) ∨ (((p4 ∧ p2) ∨ p2) ∨ ((True ∧ False) → p2))) := by
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
theorem thm_5_vars_346372839238031609722821165460 : (p3 → ((p4 ∧ (((((p4 ∨ p3) ∧ ((True ∧ (p4 → p2)) → (p1 ∨ (True → False)))) ∨ p4) ∨ (p4 → (p5 ∧ p4))) ∧ False)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165511378090438216332320506508 : ((((((False ∨ p1) ∧ (p2 ∧ (p5 ∨ p3))) ∧ p3) → p3) → ((True ∨ p1) ∧ (p4 ∧ p2))) ∨ (((False ∧ p2) ∧ (True → (p1 ∨ True))) → False)) := by
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
theorem thm_5_vars_185096269720400554213499933082 : (((p5 ∨ p5) ∨ ((p2 → p5) ∨ ((p5 → False) ∨ (False ∨ p2)))) ∨ ((p5 ∨ (p2 → (p5 ∧ p2))) ∨ (True ∨ (p4 ∧ (p5 ∨ (p1 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590156869644221197585568816655 : ((((((p5 ∧ ((False ∧ ((p5 ∧ p2) ∨ p2)) ∧ p4)) ∨ (((p3 ∧ (p2 ∨ p1)) → False) ∧ ((p2 → (True ∧ p2)) ∨ p3))) → False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337362214077715478196863341151 : (p1 → (((((True → (((True → (p3 ∨ False)) ∨ False) → (p3 ∧ p3))) ∧ (p2 ∨ False)) ∧ p5) → ((True → p2) ∧ False)) ∨ ((p1 ∨ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137197567418936880059680167825 : ((False ∧ (p2 ∧ ((((p3 ∧ p4) ∧ (True ∨ p2)) ∨ p3) ∧ (False → ((((False ∧ p1) ∧ False) ∧ p2) → (False → p1)))))) ∨ (p3 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317848692717129252512777451879 : (p4 ∨ (((p1 ∧ p4) ∧ ((True → (p2 ∨ (p1 ∧ (((p3 ∨ (False ∧ ((p1 → p5) ∧ (p3 → (p3 ∧ p4))))) → p2) ∧ p1)))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150065651159280336043930829257 : ((True → (((((p5 ∨ p1) → ((p2 ∧ (p2 ∨ p2)) ∨ p1)) ∨ p3) ∨ True) ∨ ((p2 → (p3 ∨ True)) ∧ p2))) ∨ (p5 ∧ ((p2 → p5) ∨ p3))) := by
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



