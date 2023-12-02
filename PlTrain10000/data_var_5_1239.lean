variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256656668800845288655952620530 : ((p1 ∨ False) → (((((False → (p1 → (p4 ∧ (p1 ∧ (True ∧ True))))) → ((False ∨ p3) → p2)) ∨ p4) ∨ p2) → ((p2 ∧ p2) ∨ (p3 ∨ True)))) := by
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
      cases h1
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168577857257939683402979596957 : ((p2 ∧ (((True ∨ False) → (False → (((p5 ∨ p4) → (p1 ∧ p4)) → True))) → (p4 ∧ p5))) → (((p2 ∧ p5) → (p2 ∧ (p3 ∧ False))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∨ False) → (False → (((p5 ∨ p4) → (p1 ∧ p4)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h5
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311959522296052031128688498170 : (p2 ∨ (p3 ∨ ((p4 ∨ p4) ∨ ((p2 ∨ (False → (p5 → p1))) ∨ (False ∨ (False ∧ (p1 ∨ ((((True ∨ p5) → (p1 ∨ False)) → p4) → p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111524853039373053318786643779 : (((((((p3 ∧ p4) ∨ (p3 ∨ ((False ∧ p2) ∨ (((True → p1) ∧ (p3 ∧ True)) ∧ p5)))) ∨ (p1 ∨ False)) ∧ p4) ∧ p1) ∨ True) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171865542023428620434321819649 : (((p1 ∧ (((p1 ∨ p4) ∧ (p2 ∧ (((p1 → False) ∧ p3) → True))) ∧ p4)) → False) ∨ (((p4 ∧ p4) → False) → (p4 → ((True → p2) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139264218640161936779709988368 : ((((p5 → p2) → (((p2 ∧ ((True ∧ ((True → p1) → ((p1 → p4) → True))) ∧ p1)) ∨ p5) → (p5 → p5))) ∨ p5) → (p4 → (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56551197279139846318799985305 : (((p3 ∨ ((p4 → True) ∨ p5)) → (((((p2 ∨ ((p1 ∧ p2) → True)) ∧ p2) ∧ (False → (p3 ∧ (p1 ∨ p1)))) → (p5 ∨ p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49180476623424099520738980120 : (((((False ∧ p2) ∧ (p3 ∨ False)) ∨ (((((False ∧ False) ∨ p2) ∨ p5) ∨ (p1 ∧ (p1 ∧ (p4 → True)))) ∨ p5)) ∨ (p2 → (True ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683929649757291833624841798483 : (((((((((p4 ∧ p3) ∧ (p2 ∨ p5)) ∨ (p5 ∧ (p2 ∨ (True ∨ p3)))) → False) ∨ True) → p5) ∨ ((p1 ∨ (p1 ∧ (False ∧ p1))) → p1)) ∨ p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677130259460898823564571728519 : ((((p5 → ((p3 ∧ ((p4 → p4) ∧ True)) ∧ (p4 ∧ (True → (True → ((p4 ∧ (True ∧ p2)) ∧ p4)))))) ∧ (p4 ∨ (p1 ∨ (p5 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111226554657864011880558817384 : ((((True ∧ p5) ∧ ((p5 ∨ (p3 ∨ (p4 ∧ ((False ∧ False) ∨ p3)))) → (p5 ∨ (p4 ∨ ((p4 ∧ (p1 → p3)) → p3))))) ∧ p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746257710597724938451291554101 : ((((p1 ∨ p5) → (((((p2 ∨ True) → (p5 ∨ ((p5 ∨ p5) ∧ (p2 → p4)))) ∨ ((((p4 → p5) ∧ p5) ∧ p5) ∧ False)) → p4) ∨ True)) ∨ p5) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118473748878046794572608767968 : ((p3 ∨ ((p2 ∨ (((False ∨ p1) → ((p4 ∧ (((p2 → p2) → False) ∧ p5)) → (False ∨ p2))) → (p5 ∧ (True → p1)))) → p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336295329870670843162329397357 : (p1 → ((((False ∨ False) ∨ ((p5 ∧ (True ∨ p3)) ∨ p4)) → (((p3 ∨ p2) ∨ (False → (p3 → (p5 ∧ p1)))) → ((p1 → p4) ∨ p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783701525282059052434719694797 : (((p3 ∨ (((False ∧ ((p4 ∧ p5) ∧ p2)) ∧ p5) ∨ ((p3 ∧ p1) ∧ ((p5 ∨ (p2 ∧ (p3 → True))) ∨ (False ∨ (p5 ∧ (True ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68694352987800215612990386360 : ((p4 → ((p1 ∧ ((((p2 ∨ (p5 ∧ p3)) ∨ (((False → p5) ∨ p3) ∨ True)) ∧ ((p1 ∧ (False ∨ p2)) ∧ p3)) ∧ True)) ∨ (p4 ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115256056492242416699379805906 : (((((p1 → p3) ∨ False) ∨ (p1 ∨ ((p5 → False) ∨ p1))) ∨ ((((True ∧ (p2 → (p5 → (p4 ∨ p1)))) ∨ True) ∧ False) ∧ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301426573528857328891362200412 : (False ∨ (((p1 ∧ p3) ∨ (p4 → p1)) → ((p3 ∧ ((False ∧ p4) ∧ ((p2 ∧ True) ∨ True))) ∨ (p2 ∨ ((p2 → (p3 → p5)) → (True ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245054690830476888333576347457 : ((p1 ∧ p5) ∨ ((((True ∧ True) ∨ (p2 ∧ p4)) → ((False ∨ p3) ∨ (((((p3 → True) ∧ p4) ∧ p3) ∨ False) ∨ False))) ∨ ((p2 → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69186186504067469378712027739 : ((p5 → ((((False ∨ True) ∧ (p3 → (p2 ∧ (p4 ∨ (p3 ∨ p1))))) ∨ p1) ∧ (((((p5 ∨ p2) ∨ p5) ∧ p2) ∨ False) → (p5 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608346523898530728056174210845 : (((((((p5 ∨ p2) ∨ (((p3 → (((p1 ∨ p1) ∧ p1) ∧ (p2 ∧ p2))) ∧ (True → True)) ∨ ((p4 ∧ p5) → p1))) ∨ p1) ∨ True) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_224887000810276314994802111262 : ((p5 → (p5 ∧ True)) ∧ (p2 ∨ (((p3 ∧ (p2 ∧ p2)) ∨ p1) ∨ ((True ∧ ((p2 → p3) ∨ (p2 ∨ p1))) → (p1 ∨ ((p5 ∨ False) ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172991852692455426776727321510 : ((p5 ∧ (((((p1 ∧ p1) ∧ (False → False)) ∧ p5) → ((False ∨ p4) ∨ p4)) → p4)) ∨ (True ∨ (p5 → (((p3 ∧ (True ∧ p5)) → p4) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61532554694139108808458256131 : ((p1 ∧ (((p1 ∨ p5) ∧ (((p1 ∧ (False ∧ ((True → p1) → p1))) → True) ∧ p2)) → (p1 ∧ ((p5 ∧ False) ∧ (True → (p2 → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743664323853062802500605630804 : ((((True ∧ p2) → ((((((((p4 ∧ p5) ∨ (True ∧ True)) ∧ True) → p2) ∧ p1) → p2) ∨ (p1 → ((p3 ∨ False) ∧ (p3 ∨ p1)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738400554040686865105499950655 : ((((p1 ∧ p1) ∨ ((True ∧ (((p3 ∧ p1) → (p3 ∨ p1)) → (p3 ∨ p4))) ∨ ((p2 ∧ ((p2 → p2) → (True ∨ False))) ∨ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50448078592404439717679409140 : (((p2 ∨ ((p2 → ((((p5 ∧ p5) ∨ (p5 ∧ False)) ∨ p2) → ((False ∨ (p1 ∨ True)) ∧ p5))) → p2)) ∨ (p4 → ((p5 → p2) → p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60730561375142003399387210899 : ((True ∧ ((p3 → ((p1 ∨ p2) ∧ p4)) ∨ ((((True ∧ (False → p5)) ∨ (p4 ∧ False)) ∧ (((p5 → p4) → p3) ∧ (True → p3))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312993085893421741318409161046 : (p3 ∨ ((((p1 → (False ∨ (p5 → ((p4 ∨ ((p3 ∨ (((p5 ∨ p3) ∧ p4) ∧ (p4 ∧ p5))) ∨ (p4 → p4))) → False)))) ∧ p2) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112254383547601830110936651441 : (((p4 ∨ (((p1 → (True ∧ (p1 → ((p4 ∧ (True ∨ (p3 ∧ p4))) ∨ p5)))) ∧ True) ∧ ((True ∧ (p4 → False)) → p5))) ∨ True) ∨ (True ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164560334646586323999372580573 : (((((p4 ∧ p5) ∨ (p4 ∨ True)) ∧ (False → (p1 ∧ ((False → (True ∧ p3)) ∨ False)))) ∧ p4) ∨ (((p4 ∨ (p2 ∧ p1)) ∨ (p5 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217703978347686260744376054929 : (((True ∧ (True → True)) → p2) → (p3 ∨ ((((False ∨ (p4 ∧ p1)) → p2) → (((p5 → (False ∨ p3)) ∧ False) ∧ True)) ∨ (p2 ∨ (p3 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (True → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246218325773638608937563215128 : ((p4 ∧ p3) ∨ ((((p1 ∨ True) ∧ p3) ∧ ((p2 ∨ p4) → True)) → (((p2 ∧ p2) ∧ p3) ∨ ((p4 ∨ (p4 → p4)) → (p2 ∨ (False → p5)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757582539465589082398066725637 : (((p1 ∧ (p3 ∧ (((p2 → ((p3 ∧ p3) ∧ (((True ∨ p2) ∧ ((p2 → p5) ∧ (True → False))) ∧ (p4 → (p4 ∧ True))))) → p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125925733015764789589947576285 : (((True ∨ p5) → ((((((True → (p5 → (True → (p3 ∨ p3)))) → p1) ∨ p1) ∧ (((p5 → False) ∧ False) ∧ p3)) ∧ True) ∧ p5)) → (p2 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233982333501415113158782572111 : ((p5 ∨ (p5 ∧ p3)) → (((((False ∧ ((p4 → p3) → (p4 → ((False ∧ p3) ∧ p4)))) ∧ p3) ∨ (False → (p4 ∨ p1))) ∨ p4) ∧ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160096957960128277090431384862 : (((p5 ∨ ((p3 ∧ False) ∧ (False → ((p1 ∧ ((p4 ∨ p4) → (p1 → (False ∧ p2)))) ∧ p1)))) → p2) → (((p1 ∨ (p5 ∨ p3)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303105938394463038533046743234 : (False ∨ (p3 → ((((p2 ∧ False) ∨ p2) ∨ (p3 ∧ ((p5 → (p4 ∧ True)) ∨ (p3 → ((((p4 ∨ p3) ∧ (True → False)) ∧ p2) ∨ p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_887861322838763584340967761754 : ((((((True → ((((False → p4) → False) ∧ False) ∧ (p5 ∨ (p4 ∧ (p5 → True))))) ∧ (p1 → (p4 → p5))) → (p2 ∧ p2)) → (False ∧ True)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → ((((False → p4) → False) ∧ False) ∧ (p5 ∨ (p4 ∧ (p5 → True))))) ∧ (p1 → (p4 → p5))) → (p2 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55528964528193964314306063480 : ((((True ∨ p3) → ((p1 ∧ p1) ∧ p2)) → ((((p2 ∧ p5) ∧ False) ∨ (p5 ∧ ((p2 ∧ p4) → (p5 → p3)))) ∨ (p2 ∨ (p4 → False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349978093508056019404925421928 : (p4 → (((((((((p3 ∨ True) ∨ (p2 → (p3 ∨ p5))) → (True → (False → (p5 ∨ False)))) → (p5 ∨ p2)) → p5) ∨ p5) ∨ p2) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55450087797265103604226368221 : ((((True ∧ (p4 ∧ (p3 ∧ False))) → p1) → (((((p2 ∧ (p2 → False)) ∧ p4) ∧ (p4 ∧ (p3 → (p3 ∧ p4)))) → (p5 ∨ p3)) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h9 := h4.left
  let h10 := h4.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232211994244780080503954503091 : (((False → p5) → p4) → (((False → (p5 ∨ (((p2 ∧ p1) → p4) ∨ (p3 ∧ (p2 → False))))) → p2) → (((p2 → (False ∧ p5)) ∨ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p5 ∨ (((p2 ∧ p1) → p4) ∨ (p3 ∧ (p2 → False))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p5 ∨ (((p2 ∧ p1) → p4) ∨ (p3 ∧ (p2 → False))))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261148292166596908081546664522 : ((p4 → p4) → ((p1 ∨ ((True ∨ (((False ∧ p4) ∨ p2) → (((False ∨ (True ∨ p2)) → (True ∧ p1)) → p3))) → p5)) ∨ (p4 → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45166472432814568948843275503 : (((True ∧ ((((p2 ∧ p5) ∧ (False ∨ (p4 ∧ (p1 → p2)))) ∨ True) → (((p4 ∨ (False → p2)) ∨ p2) ∨ (False ∨ (p2 ∧ p4))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248256083144061213720752133608 : ((p2 ∨ p2) ∨ ((((p2 ∨ ((p3 ∧ (p3 → (p1 → (False ∨ (((False ∨ p4) → False) → ((True ∧ p4) ∨ p3)))))) ∨ False)) ∨ p5) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115145928066716541051993109468 : (((p5 ∧ (((p3 → (True ∧ (p5 → p1))) ∧ True) ∧ (p4 → p4))) → (p2 ∨ ((p4 → (True ∧ ((p5 ∨ True) → p2))) ∧ p4))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809580617215568929643597228292 : (((p5 → (((p5 → p4) ∨ (p4 ∧ (((p5 → (False → (True ∧ True))) ∧ (True ∨ p2)) ∧ (p3 → ((p2 → (p3 ∧ p1)) ∨ p5))))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68740144774026197906387659433 : ((p4 → ((p4 → (True ∧ (True → ((False ∨ (True ∨ (((p2 ∨ True) ∨ (p3 ∧ True)) → p5))) ∧ p4)))) → ((p5 → (True → False)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40609297955518671779226369753 : ((((((p5 → ((p1 ∨ p4) → (((p2 → True) ∨ False) → (False ∨ (p1 ∧ p5))))) ∧ (p3 ∨ ((p3 ∨ p1) → True))) ∨ p2) → p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600352503032202970948376522100 : ((((True ∧ ((True → ((p5 ∨ (False ∧ ((p2 → p2) → False))) ∧ (False → ((p1 → (True ∨ p3)) ∨ ((True ∨ p3) ∨ p3))))) ∧ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320049557026728012707151100522 : (p4 ∨ ((p3 ∧ (p2 ∨ p2)) ∨ (((True → p3) ∧ (p1 → True)) ∨ (((p1 → (p3 → ((((False → p4) ∨ False) ∨ p2) → p5))) ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_53067721335099876210650370232 : (((p1 ∧ (((p4 → p1) → (p4 ∨ ((p2 ∨ p1) ∧ False))) ∨ p4)) ∧ (((p5 ∨ p5) ∧ True) → (((p2 → (p3 ∨ p4)) ∧ p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226216107813413014824689330308 : (((p2 ∨ p3) ∨ p2) ∨ ((p5 ∨ (((p1 ∨ (p5 ∨ (p3 → (True ∨ (p3 ∧ (p1 ∧ p3)))))) ∨ p3) ∨ True)) ∧ (((False ∨ True) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720399078114900056845342430445 : ((((((False → p1) → p5) ∨ p4) → (False ∨ (((((p2 → p1) ∨ (p5 ∨ p5)) ∧ ((p1 → p2) ∧ p1)) ∧ (p4 → (p2 → p3))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762564285649058255073373676776 : (((p3 ∧ (((((p3 ∨ (p3 ∧ ((p5 ∧ p3) → p1))) → (p2 ∨ (p4 → p5))) ∧ p3) → False) → (p1 ∨ (False ∨ ((p2 → p3) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317805135717130406244495036441 : (p4 ∨ ((((p4 ∧ ((False ∧ False) → p5)) ∨ p5) ∧ (((p3 → (True ∨ (True ∨ (p1 ∨ (True → (True ∧ p1)))))) ∧ (p5 ∨ True)) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313089719664086596941105238430 : (p3 ∨ (((p1 → (((p4 → (False ∨ p4)) ∧ (p3 ∧ False)) ∧ (((p2 ∨ p1) ∨ p4) ∧ ((True ∨ (p3 → False)) ∨ True)))) ∨ (p1 ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57741012868787920449490293000 : ((((p5 ∨ p2) → False) → (((((p3 ∨ (p1 → (p4 ∨ p3))) → ((((p4 → p2) ∨ (p2 ∨ p2)) → p4) ∧ True)) ∨ p3) ∨ p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315174249384231495842035683062 : (p3 ∨ ((p3 ∨ (p4 ∨ (p4 ∨ (p1 ∧ p3)))) → ((p5 → ((((p1 ∧ (p4 ∧ p2)) → True) → p3) → p2)) → (p4 ∨ ((p4 ∨ p3) ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330250670377171040846620716124 : (True → (False ∨ ((((p4 ∨ (True ∧ p2)) ∨ (((p4 → ((False ∨ p2) ∨ p5)) ∨ p1) ∧ p3)) ∧ ((p3 ∧ p1) ∧ True)) ∨ (False → (False ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215949246780284268790692989900 : ((p4 ∨ ((p1 ∨ p3) ∧ p1)) ∨ ((((((p2 ∨ p4) ∨ (p3 ∧ p3)) → (p1 → p3)) ∨ p2) ∨ (((p5 ∨ True) ∨ (p1 → p1)) ∧ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_186661769687640858719165386720 : ((((p2 → (p3 ∨ (p5 → p3))) → True) ∧ ((False ∧ p2) → p2)) → (p4 ∨ (((p5 → (False → True)) → p5) → ((p3 → p4) ∨ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → (False → True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134830766303248771626879770370 : (((p2 ∨ (((True ∨ ((p4 ∨ (p5 ∨ p4)) → ((False ∨ p2) ∨ ((p5 ∨ p1) ∨ (p4 → p4))))) ∧ p1) ∨ True)) → False) ∨ ((p2 → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157733752362135923614352023410 : (((False → ((((True ∨ p5) → p1) → p2) → ((p1 → (p4 ∧ p4)) ∧ p3))) → (p3 ∧ (False → p3))) ∨ (p2 → ((True ∨ p2) ∨ (p2 → True)))) := by
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
theorem thm_5_vars_123688944657091842739357336338 : (((p5 ∨ ((False ∨ ((True ∧ ((True ∧ (p1 ∧ p5)) ∧ (p2 ∧ False))) ∨ True)) ∨ False)) → (p5 ∧ (True → ((True → p4) ∧ p1)))) → (p5 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((False ∨ ((True ∧ ((True ∧ (p1 ∧ p5)) ∧ (p2 ∧ False))) ∨ True)) ∨ False)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ ((False ∨ ((True ∧ ((True ∧ (p1 ∧ p5)) ∧ (p2 ∧ False))) ∨ True)) ∨ False)) := by
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
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810777348284200056425315703802 : (((p5 → ((p4 ∧ p4) ∧ ((((((True → p3) → (p4 → (False ∨ ((p4 ∧ (p2 ∧ p3)) ∨ p3)))) ∨ p5) → True) → p4) ∧ (True ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147086861295226279186756359811 : ((((p4 ∨ ((p5 ∧ p4) ∨ p2)) ∨ (((p2 ∧ p2) → (((p1 ∨ (p5 ∧ False)) ∨ True) → p2)) → p4)) ∧ p5) ∨ (p4 ∨ (True ∧ (p3 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183878304311291027530546412993 : (((((p1 ∧ p5) ∧ p1) ∨ ((p3 → p3) → (False ∨ p4))) ∧ p4) ∨ (((p2 ∧ False) ∨ (p4 ∧ p5)) → ((p4 ∨ (False ∧ (True ∨ True))) ∧ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303413577427541137793905715298 : (p1 ∨ (((((((p1 ∧ (True ∨ p2)) → p2) ∨ (p2 ∧ True)) ∧ p1) → ((p4 → (p4 ∧ p5)) ∧ (p3 ∨ (True ∧ p2)))) ∨ (p2 → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_191544015297582969251339735613 : ((p1 ∧ (((p1 ∧ p3) → (p1 ∧ p5)) ∨ (False ∨ p1))) ∨ ((((((False ∨ p5) ∧ p2) ∨ (p2 ∧ p2)) ∨ p3) → (p3 ∨ p4)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219016985273370646820189877465 : ((p4 ∧ (p4 → (p5 ∨ False))) → ((p5 ∨ (((p3 → p1) ∧ (p2 ∨ ((((p4 ∧ True) → (True ∧ p3)) → p5) ∨ p4))) ∨ (False → p5))) ∨ p4)) := by
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
theorem thm_5_vars_153418735300460667128251187935 : ((p3 ∨ (p5 ∨ ((((False → ((p2 ∧ p5) ∨ (((p2 → p2) → p5) ∧ True))) ∧ p5) ∨ (p5 ∧ p1)) ∧ p4))) → ((p4 → p1) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751851877503665703223020890769 : (((True ∧ (p1 ∨ ((p1 ∨ (p5 ∧ True)) → ((((False ∨ p5) → False) ∧ ((p5 ∧ (p5 ∧ p3)) ∧ ((p1 ∨ (p5 ∧ p4)) ∨ p2))) ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127815931886312867330584848130 : ((True → (p3 ∧ (((p3 ∧ p5) ∧ ((p1 ∧ p2) → False)) ∧ (((p2 → (False → (p1 ∧ False))) → p4) ∧ ((False ∧ p3) ∧ p2))))) → (p2 ∧ p5)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481080301728981771514946922065 : (((((p4 ∨ p3) ∧ ((p1 ∧ (p3 ∧ p4)) ∨ p4)) ∨ (p5 → ((p3 → (((p2 → (p5 ∨ (p5 ∧ True))) → True) ∨ (False ∧ p2))) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802526692917373143611281006106 : (((p2 → (p3 ∨ (p1 ∨ (((p2 → p5) → ((p4 ∧ True) ∧ (p1 → (p3 ∧ True)))) → (((p5 ∨ (p4 ∧ False)) ∨ (p1 → True)) ∨ True))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47124398554133112010690358686 : ((((((((p2 ∨ p1) → ((p3 → (False → p1)) → p3)) ∧ (True ∧ p2)) → (p5 ∧ False)) → p1) → (True → (p1 ∨ p5))) ∨ (False → False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637459630961523664658239753745 : ((((((False → p5) → (p1 ∧ ((p4 → (False ∧ p1)) ∧ p5))) ∧ ((p4 ∧ ((p4 ∧ (True ∨ (p5 → (p4 → p2)))) ∨ p3)) ∧ p5)) → False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h21
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h27 := h25 h26
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h30 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h31
      -- False on the left can always be used.
      apply False.elim h31
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h30
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h35 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h36 := h34 h35
    -- We need to get the left conjuct of h36 based on <expert-advice>.
    let h37 := h36.left
    -- False on the left can always be used.
    apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629220991175182514875500416200 : ((((((False → ((p1 ∨ (p3 ∨ ((True ∨ p1) ∨ True))) ∧ (False → (True ∧ ((((p1 ∧ p2) → p1) ∧ True) → p5))))) ∨ p2) ∨ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163165627701855743396633181443 : (((((p3 ∧ p1) → p3) ∧ ((p4 ∨ True) → (p3 ∨ p3))) → (p2 ∨ ((p5 ∧ True) ∨ p3))) ∧ (False → ((p4 → (p1 ∨ (False ∧ p1))) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149281549692704704392140299283 : (((p2 → p1) ∨ (((False ∨ ((((p1 ∧ False) → True) → (p2 ∨ (p3 ∨ p4))) ∨ True)) ∧ (True → True)) ∨ p3)) ∨ (((p2 ∧ p1) → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72187589241169634969651455271 : (((p1 → (((p5 → ((((p4 ∧ p4) → p1) ∧ (p1 → (p2 → ((p5 → p1) ∧ p2)))) ∨ p5)) ∧ ((p5 ∧ p3) ∧ False)) ∧ True)) ∧ p1) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193264507769463235201323716319 : (((True → (p4 ∧ p5)) ∧ (p3 ∨ ((False → p2) ∧ False))) → (((p2 ∧ (p3 → p1)) → (((p5 → (True → p4)) → (True ∧ p5)) ∧ p5)) ∨ p4)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228117161065972701055454268312 : ((p4 ∧ (p5 ∨ p2)) ∨ (p3 → (((True → (p1 → ((p1 → p5) ∨ (p2 ∨ (p2 ∨ p4))))) → ((p2 ∨ False) ∨ (False ∨ (p3 ∨ p5)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357416298584639424940871114893 : (p5 → ((p1 ∨ p3) → ((True → (((p4 → p4) → False) → (False ∧ (p4 ∧ ((False ∨ False) ∧ (((p3 ∧ p2) ∨ p3) ∧ False)))))) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342144085463467323285279926256 : (p2 → ((((p1 ∨ ((((p2 ∨ p3) → p2) → p3) ∧ ((True → (False ∨ p5)) ∨ p3))) ∨ (p3 ∧ True)) ∨ True) ∨ ((True ∧ p3) ∧ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147879307633276831466894745234 : (((p5 → ((((p3 ∧ (((p4 ∧ False) → p2) ∧ (False → p3))) → p5) → True) ∨ ((p4 ∨ p2) ∧ p3))) → p4) ∨ (((p3 ∨ False) ∧ p3) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806325444166140962136168224591 : (((p4 → (((p1 ∨ p3) ∨ ((((False → (((p1 ∧ p2) → p2) → (p4 ∨ p2))) → (p5 ∧ ((p1 ∨ p5) ∧ p4))) ∧ True) → p2)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_703391644484108202253473879743 : ((((p1 ∨ (p3 ∨ (((p4 ∨ (True ∨ p2)) → p1) → p4))) ∨ (p3 ∧ (True ∨ ((((p3 ∧ (p4 → True)) ∧ False) ∧ (p5 ∧ p3)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51883165234761846072330325360 : ((((((p4 → p2) ∨ ((p1 → (p5 ∨ (False ∨ (False → p3)))) ∨ p3)) ∨ False) → p5) ∨ ((True ∧ p5) → (p1 ∨ ((p5 ∨ p5) ∧ p5)))) ∨ p4) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127193155789637714834868328175 : ((p1 ∨ (((((p1 ∨ p1) ∨ (True → p4)) → p5) ∧ (p4 → p5)) → ((True ∨ p1) ∧ (((p3 → (False → p2)) ∧ p4) ∨ True)))) → (p2 ∨ True)) := by
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
theorem thm_5_vars_596780849125638245103474059054 : (((((p4 → ((p1 ∧ True) ∧ (True → p2))) ∧ ((p5 → p1) → ((p2 ∨ ((p3 ∨ (False ∨ (True ∨ True))) ∧ False)) ∧ (p5 ∧ True)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231267347668044443107286424578 : (((p4 ∨ p5) ∨ p4) → ((((((p3 ∧ p4) → p4) → p3) ∨ (p1 ∨ p3)) ∧ p2) → ((((p2 → p5) ∨ ((p1 ∧ p1) ∨ p1)) ∨ p5) ∨ p3))) := by
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
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h8 : ((p3 ∧ p4) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h9
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h12 := h5 h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 ∧ p4) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157793118595883875307718526365 : ((((False ∨ True) → (p2 ∧ ((((p1 → p5) ∨ p2) ∧ p1) → False))) ∨ ((p2 ∨ (p1 ∨ True)) ∧ p1)) ∨ (True ∨ (p4 ∧ (p5 ∧ (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252098087048316766381290772193 : ((p4 → p2) ∨ (((p1 ∨ ((p3 → (p2 ∨ (((p3 ∧ False) ∨ (p1 ∧ (False ∨ (p1 → p4)))) ∧ p4))) ∨ False)) ∨ True) ∧ (False → (False ∧ True)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64757045034022063299314998477 : ((p2 ∨ (((False → False) ∧ (((p2 → (p4 ∨ False)) ∧ p5) ∧ (p4 ∨ ((((p1 ∧ p1) ∨ (p2 ∧ p3)) → p3) ∨ (True → p3))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168159273470557679828089425968 : ((((False → p3) ∨ p1) ∧ (p4 ∨ (True → (p5 ∧ (True ∨ ((p5 ∨ p3) → (p2 ∨ p3))))))) → ((True → False) → (False ∨ (p4 → (p2 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174836604839295781419897909471 : (((p4 ∧ p1) ∨ ((((p2 → p5) ∨ (p2 ∨ ((p3 → p1) ∨ False))) → p1) ∧ p3)) → ((p5 ∧ p2) ∨ ((p3 ∧ (p2 ∨ (True ∧ True))) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45631952175325797549626203230 : (((p4 ∨ ((False → (False ∧ ((((((p2 → (p5 ∨ p3)) ∨ (False ∧ False)) → True) → (True → p3)) ∧ p1) ∨ p2))) ∨ (p5 ∨ p1))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



