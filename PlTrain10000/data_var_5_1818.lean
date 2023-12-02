variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166394007371977417126398359994 : ((False ∨ ((p5 ∨ p5) ∧ (((p3 ∨ (False ∨ p5)) → (p2 ∧ p4)) → ((False → p4) ∧ p2)))) ∨ ((False → p3) ∨ (((p2 ∧ False) ∧ p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160571015191801530980149022257 : ((((False → (True ∨ p5)) → (p5 ∨ (False → (False ∨ (True ∨ p1))))) → (p3 ∨ (p2 → (p1 → p4)))) → (((p2 → p5) → p4) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673743930131796985595256328451 : (((((False → p5) ∧ ((((p4 → (p3 → False)) → False) → (True → p2)) → (False → ((p4 ∨ (True ∧ True)) → p3)))) → (p2 ∨ (p2 → p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242815482880384488010068300413 : ((p3 → p3) ∧ ((p4 → (p4 ∨ (((p3 ∨ (False ∧ False)) → p2) ∨ p4))) ∧ (True → ((((p3 ∨ p3) ∨ ((p3 → True) → p3)) ∨ True) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190249083941074099795604525601 : (((((p5 → p4) → (p5 ∨ (p5 → p3))) ∧ p5) ∨ p1) ∨ (((False → p5) → (p2 → (True → (p4 → (p2 → (p3 → (p3 ∧ p2))))))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337141575505992433434881874441 : (p1 → ((True → (((True → ((True ∧ (p5 → p2)) ∨ (p2 ∨ (p3 ∧ False)))) ∨ False) ∨ (((True → (True ∧ p4)) ∧ p2) → p3))) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49509814996854968012140850610 : ((((((False → (((True ∧ (p2 ∧ (p5 ∧ (p5 ∧ (p4 → True))))) → True) ∧ False)) ∨ False) ∧ p4) ∧ (True ∨ True)) → ((p5 ∧ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64981569814371119604393750921 : ((p2 ∨ ((p2 → ((p3 ∨ False) ∨ p3)) ∨ (p2 ∨ (((p5 ∧ p3) → p3) ∧ ((False → (True ∧ False)) → (True ∨ ((p2 → p3) → True))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75669807249045721445205925639 : (((((((((p5 ∨ ((False ∧ False) ∨ True)) ∨ (p4 ∧ (True ∨ p2))) ∧ (p3 → p5)) ∨ p5) ∨ ((p5 ∧ p5) ∨ p5)) ∨ p3) ∨ True) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p5 ∨ ((False ∧ False) ∨ True)) ∨ (p4 ∧ (True ∨ p2))) ∧ (p3 → p5)) ∨ p5) ∨ ((p5 ∧ p5) ∨ p5)) ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194869690365176217463018436199 : ((((p2 ∨ (p3 ∨ (p1 ∧ p4))) ∨ p2) → True) ∧ (True ∧ (p2 ∨ ((((((False ∧ p2) ∧ p4) ∧ p5) ∧ ((True ∧ p1) ∧ p2)) ∨ True) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_309519576723584105547566278689 : (p2 ∨ ((p5 ∨ (((((True → (((p2 ∨ p5) → (p2 ∨ p3)) ∧ (p5 → (p4 ∨ p5)))) → p2) ∧ p4) ∨ p2) ∨ (True ∨ False))) → (False ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251862071099146276499902645755 : ((p3 → p5) ∨ ((((p1 → (p4 ∨ p1)) → ((p2 ∨ ((False → p1) ∨ p1)) → False)) ∧ p3) → ((True → ((p2 ∨ (p1 → False)) ∧ p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (p4 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ ((False → p1) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208985870933381553625161935456 : ((True ∨ (p2 → (p5 → (True ∨ p4)))) → ((p2 ∨ (True → False)) ∨ (((p4 → (True ∧ False)) → p2) → ((True ∧ True) ∧ (p5 → (p5 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337092887529661832315241826999 : (p1 → (((((p3 ∧ p3) ∨ p5) → ((p2 ∧ (p3 → p4)) → False)) ∨ (p1 ∨ (True ∨ ((p3 → p3) ∨ ((p1 ∧ False) ∨ p4))))) ∨ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51421717424812607114368140553 : ((((p5 → (p1 ∧ ((p3 → (True ∨ (p4 ∧ (p4 ∨ ((True ∧ False) ∧ p5))))) ∨ p3))) → p4) → ((p5 → p3) ∧ ((False ∨ p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52970218755223191629788030401 : (((((p3 ∨ ((p1 ∨ p1) ∨ (True ∧ p5))) → (p3 ∨ p4)) → False) ∧ (p4 ∨ (((p1 → (p5 ∧ p1)) → False) ∨ ((p3 ∧ p1) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54529697075266369667455214266 : ((((p4 ∨ False) ∨ (((p5 → False) ∧ p3) ∧ False)) ∨ ((True ∨ (p3 ∨ p4)) ∨ (False ∨ ((((False ∧ p4) ∨ True) ∧ p2) ∨ (p2 ∧ True))))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215764520243806483878535025612 : ((p1 ∨ ((True → p3) ∨ p2)) ∨ ((((p1 ∨ True) ∧ (p3 → (False ∨ (p5 ∨ (p3 ∨ (p1 ∨ (p4 ∧ p4))))))) → ((p3 ∧ p1) ∧ p5)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ True) ∧ (p3 → (False ∨ (p5 ∨ (p3 ∨ (p1 ∨ (p4 ∧ p4))))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208555965184835051514784058131 : (((p3 ∨ p2) → (p1 → (p2 → p5))) → (((p3 ∨ (p4 ∨ ((p5 ∨ p4) → True))) → False) ∨ (((p4 ∨ ((p4 → p5) → p4)) ∨ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248381928039456427878854487477 : ((p2 ∨ p4) ∨ ((p4 ∧ ((p4 → True) → ((p3 → (p2 ∧ (p5 ∧ p4))) → ((p5 ∨ (((p4 → p4) ∧ (p2 ∨ p4)) ∧ p1)) ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343165249393134033645457737125 : (p2 → ((p3 ∧ (p1 → p3)) ∨ ((False ∧ ((((p5 ∨ p4) ∧ p1) → (p3 ∨ (p4 ∧ ((p2 ∧ (p2 → (p3 → False))) → True)))) ∧ p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168010404146810306593568001855 : (((((p1 ∧ False) → p3) ∧ (p1 → p2)) ∨ (p4 → ((p3 ∨ (p2 → p1)) → (p5 ∧ p5)))) → (p5 ∨ (((False → False) ∧ (p4 ∧ p2)) ∨ True))) := by
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
theorem thm_5_vars_57885364035553799079970042327 : (((p2 ∨ (p4 ∨ False)) → ((p5 ∧ (((p4 ∨ ((True ∨ (p3 ∨ (p1 ∧ p5))) ∨ p1)) ∨ p3) → p3)) ∨ (p1 ∨ ((True ∧ True) ∨ True)))) ∨ p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38096403159362854557167242641 : ((((p5 ∨ ((p5 → p4) → (((((True ∨ (p4 → (True ∨ p3))) → p1) → (True ∧ p5)) → p3) ∧ (p5 → p4)))) → (p5 → p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148326995413609754001080643251 : (((((p1 ∧ p3) ∧ ((p4 → ((p4 → False) → p3)) ∨ (p2 → p1))) ∧ True) ∧ ((p5 → False) ∨ (p4 ∨ p4))) ∨ ((p5 ∨ (True → True)) ∨ p1)) := by
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
theorem thm_5_vars_607248368512639051351682582599 : (((((((p1 → (p4 → False)) ∨ p1) → (((p4 ∧ True) ∨ p3) ∨ (p1 ∨ (p2 ∨ (True ∧ ((p2 ∨ (p2 ∨ p3)) ∨ False)))))) ∧ p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186045940861850705441717871526 : ((((False → ((p3 ∧ (False ∨ p1)) ∧ (p1 → False))) ∧ p1) ∨ p4) → ((p4 ∨ ((False → ((False ∨ (p4 → True)) ∧ p4)) → (p2 ∨ p4))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350167612133041265911209117130 : (p4 → ((((False ∨ p5) ∧ (p3 ∧ (p5 ∨ p1))) ∧ (True ∨ ((p1 ∧ ((p4 ∨ p5) ∨ ((p3 ∧ p3) ∧ p1))) ∨ (p1 → (p5 → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595060132659327834554874790643 : (((((False ∧ (False ∧ (((p2 → p3) ∧ p5) ∨ ((p3 ∧ (p2 → False)) ∧ p1)))) ∨ (((p5 ∧ p1) ∨ p1) → ((p5 ∧ p3) ∧ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669880984124736063444939318865 : (((((((p2 ∧ (((p5 → p3) → p5) ∨ (p1 ∧ p1))) ∨ True) ∨ p4) → ((True ∨ ((p1 ∧ p1) → False)) → p2)) ∨ ((p2 → p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620197991255873338140959219219 : (((((p3 ∧ p3) ∨ ((False ∧ ((p4 ∧ False) → (((p3 ∧ p2) ∨ (p1 ∨ ((p3 → (p3 ∨ True)) → p1))) ∨ p5))) ∨ (p5 ∧ False))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_819932041965959249107665521357 : (((((((p5 ∨ p2) ∧ (False ∨ (((p1 ∧ p3) ∧ ((p1 → True) ∨ p3)) → (False ∧ True)))) ∨ (True ∨ p4)) → (False ∧ (True ∨ p1))) ∧ p1) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∨ p2) ∧ (False ∨ (((p1 ∧ p3) ∧ ((p1 → True) ∨ p3)) → (False ∧ True)))) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207691738624295719207265502194 : ((((p5 ∨ p5) → (p5 ∨ p1)) → p1) → (p3 ∨ (((p4 ∨ ((((p4 ∨ p5) ∨ p3) ∧ True) ∨ ((False ∧ p4) → (p3 ∧ p1)))) ∨ p1) ∨ p4))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708266479057331614100459110535 : ((((p5 → ((((p2 ∧ p4) ∨ p4) ∨ p2) ∧ p1)) ∨ ((p1 → ((p5 ∧ p5) ∨ ((p4 ∨ (p5 → False)) ∧ p3))) ∨ ((p5 → True) ∨ True))) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116373942973902171944207548195 : ((((p3 ∨ p4) → True) → (p4 → (((p4 ∨ (((p3 ∨ p3) → False) → (True → (p1 → True)))) ∧ (p3 ∨ False)) ∨ (p2 ∧ p4)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191193207869504891085318267453 : ((((p4 → False) ∧ True) → ((p2 ∨ p2) ∨ (p1 ∨ p1))) ∨ (((True ∧ (p3 → p2)) ∧ ((((False ∧ False) ∨ p4) ∨ (True ∨ p3)) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353381737126001727520391723616 : (p4 → (False ∨ (((True → p5) → p5) → (p1 ∨ ((((((p5 → (True ∧ False)) → ((p4 ∨ False) → p1)) ∨ True) ∨ p2) ∧ p4) ∨ (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218044757330872429922329263135 : (((p2 ∨ p3) ∧ (p1 ∧ p4)) → (((p3 ∧ ((p5 ∧ p4) → p2)) → p1) → ((p4 ∧ p1) ∧ (False ∨ (((False ∧ False) ∨ True) ∨ (p2 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h12.left
    let h18 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h20.left
    let h26 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42844919043496619413539570407 : (((p2 → (((((p2 → p1) → (((p1 → ((p2 → p4) → (True ∧ p5))) ∧ p5) ∧ (p4 ∨ p2))) → p4) → (p2 → False)) ∨ True)) ∨ p4) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40110021863293804214768421616 : (((((((p2 ∨ (p1 ∧ p1)) ∨ (False ∨ p4)) → (p1 → ((p5 ∧ ((p2 ∨ p4) ∨ p5)) → (p2 ∨ p2)))) ∨ (False ∨ p4)) ∧ p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358535836723607863765430141456 : (p5 → (p2 → ((False ∧ (((False ∧ (((p2 ∧ p5) → p3) → (((p4 ∨ False) ∨ False) ∧ False))) → p5) → (p1 → p4))) ∨ ((False ∧ True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133803218367286860878157920822 : ((((p4 ∨ (p4 ∨ True)) → ((p3 ∧ (p3 → p1)) ∧ (((p5 ∧ p5) ∧ False) ∨ (((p1 ∨ p1) ∧ p2) ∨ p4)))) ∧ p4) ∨ ((p5 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227334081519238748788641490142 : (((p3 → True) → p1) ∨ (((True → ((p1 ∨ ((p4 ∨ (p4 ∨ (p1 ∨ p2))) → p4)) ∧ p5)) ∧ (p2 ∧ ((p4 → (p5 → p3)) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780934971051820582152822883006 : (((p2 ∨ ((False ∧ (p5 ∨ p4)) ∨ (p2 ∧ ((((p5 → True) ∧ ((p3 ∨ (True → (p1 → (p1 ∧ (p4 → p5))))) → p1)) ∨ p2) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45931434236067155860319234769 : (((p4 → (p1 → (((p4 → (((p4 → ((False → p2) → p5)) → p5) → True)) → False) ∧ ((False ∨ (True ∨ (True → p4))) ∨ p4)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177931475346115415926227266334 : (((((p1 ∨ p3) ∧ (p3 ∧ p3)) ∨ ((p4 ∧ p4) ∧ (p1 ∧ True))) ∨ p4) ∨ (((False ∨ (True ∨ (p1 → (p5 ∨ p4)))) ∨ (p4 ∧ p5)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49283181536055442160717523469 : (((p4 ∧ ((p2 → p5) ∧ (p2 ∨ ((((p3 ∧ (p1 → (p1 ∨ (p3 → (p2 ∨ p5))))) ∧ False) ∧ False) ∧ p4)))) ∨ ((False → False) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356045826832415811360491111153 : (p5 → ((False ∨ ((False ∨ (((False ∨ (p1 → (p2 ∨ ((False → False) ∨ False)))) → p1) → (p5 → p1))) ∨ True)) ∨ (True ∧ ((p1 → False) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336120126577718700994594225198 : (p1 → ((((True → (p3 ∨ ((p3 → ((False ∧ (p4 ∨ p2)) ∨ (False ∧ p3))) ∨ ((p3 → False) ∧ p1)))) ∨ ((p2 → p4) → p5)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729835697450642883512618132332 : (((((False ∧ False) → p2) → ((((p4 → p1) → ((p2 ∨ p1) → (p2 → p3))) ∧ (((p1 → True) ∨ (True → (True ∧ False))) ∨ p3)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_116568217090475058106578429473 : (((p2 ∨ p4) ∧ (False ∧ (((p2 ∨ p4) → ((p1 ∨ p4) → (True → ((p5 ∧ (p2 ∧ p4)) ∨ p2)))) → (p1 ∧ (p3 ∨ p1))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173815827247557558263563025978 : (((False ∨ ((p1 ∧ ((p4 → (p1 → (p2 → p4))) ∧ (p3 ∨ p4))) ∧ False)) ∨ p4) → (((p2 ∨ ((True → (False ∧ p2)) ∧ p5)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h6
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313990353108939741143043721909 : (p3 ∨ (((p5 ∨ (False ∨ p2)) ∧ ((p3 ∨ False) ∧ ((p4 ∧ (((p4 ∧ ((False → p5) → (p4 ∨ False))) → p2) ∧ p2)) → p2))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736190159593999456594269885920 : ((((False → p1) ∧ ((((p1 ∧ p2) ∧ (p1 ∧ (True → (p4 → False)))) ∧ (((True ∧ p2) ∨ (p3 ∨ p3)) ∨ (False → True))) → (p5 ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197267968750188903743007014190 : ((((True ∧ (True ∨ False)) ∧ (p4 ∨ True)) → p4) ∨ (p2 ∨ (((p1 ∨ p3) → ((p4 ∧ (False ∨ p1)) ∧ (p4 → p1))) ∨ ((p3 ∨ True) → True)))) := by
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
theorem thm_5_vars_157080599165499820793161740647 : (((p3 ∨ ((True → (p2 → (p3 ∨ p4))) ∧ ((p5 ∨ (((p3 ∨ p2) ∧ p5) ∧ p5)) ∨ False))) ∨ p3) ∨ (p5 → ((p5 ∨ (p3 ∨ p2)) ∨ p1))) := by
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
theorem thm_5_vars_660265439570636261952832175269 : ((((((p5 ∧ False) → (p3 → (False → (((False ∧ p1) → False) ∧ (((False ∧ True) ∧ (True ∨ (False → p3))) → False))))) ∨ p2) → (p1 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65515528963296177774955151352 : ((p3 ∨ (p1 ∨ ((((p3 → (((p3 ∨ True) ∨ ((p5 ∧ (False → (p2 → p5))) → p2)) ∨ (p3 ∧ p1))) ∧ p3) ∧ p2) ∨ (False ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193814760107037482121391777843 : ((p5 ∧ (((p4 ∧ p4) ∨ (p1 → p2)) ∧ (p5 ∨ p3))) → ((p1 ∨ (p1 ∨ (((p5 → p2) ∨ (True → False)) ∨ p2))) ∨ (p3 ∨ (True ∧ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125015816245686901419322466448 : ((((p1 ∨ p4) ∨ p5) ∧ (p5 ∨ (True ∨ (((True ∧ ((((p1 ∧ p3) → p4) ∧ p5) → p1)) ∧ True) ∧ ((p4 ∧ p1) ∧ p4))))) → (p3 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h11.left
          let h17 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h16.left
          let h19 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h25.left
          let h28 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h27.left
          let h30 := h27.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h26.left
          let h32 := h26.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h31.left
          let h34 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h40.left
        let h43 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h42.left
        let h45 := h42.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h41.left
        let h47 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h46.left
        let h49 := h46.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192280362997296333275998056967 : ((((p3 → p3) ∧ (p1 ∧ (p4 ∨ (p2 → p4)))) ∧ p3) → (p2 ∨ (True ∧ (p3 → ((((p5 → ((p4 ∧ p4) ∨ p1)) → p1) → False) ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262538696702153175734337620761 : (True ∧ (((((p2 ∨ (((p2 ∧ (p2 ∨ p3)) ∧ (p4 → p1)) ∨ ((p3 ∧ p5) ∨ p1))) ∨ True) → (p5 ∧ (False → (False ∧ p4)))) ∧ True) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (((p2 ∧ (p2 ∨ p3)) ∧ (p4 → p1)) ∨ ((p3 ∧ p5) ∨ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205222131511787864998536577376 : ((((False ∨ p1) ∧ True) ∨ (True → False)) ∨ (((p3 ∨ ((True → p1) → ((True ∧ ((p4 → p1) ∨ ((False → p5) ∨ p1))) ∨ p1))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165897649932220015460982986865 : (((p3 ∧ (False → p2)) → ((p5 ∧ (((False ∨ (p5 ∧ True)) ∨ p1) ∧ (True ∧ p5))) ∧ p3)) ∨ ((p4 → (True ∧ ((p4 → False) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201205434395311773638517901052 : ((p2 → (((p3 → (p2 → p5)) ∧ p4) ∧ True)) → (((p5 ∨ p4) ∧ p1) ∨ (p5 ∨ (((False ∨ (False → p2)) ∧ (p5 → False)) → (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219741747842020627205034720915 : ((p1 → (p2 → (p4 → p5))) → ((((p2 → (p3 ∧ (p5 → p1))) → (p1 ∨ (p2 ∨ ((p3 ∨ p1) ∨ (p2 → True))))) ∨ False) ∨ (p1 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178457895198045448278102728023 : (((p4 ∧ (((p1 ∨ p3) → (p5 ∧ p3)) ∧ p1)) ∧ (p5 ∨ (False ∨ False))) ∨ (((False → True) ∧ p3) → (((p2 → True) ∧ p1) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_263884635168142231320365670066 : (True ∧ (((p5 ∧ ((p1 → p1) → (False ∧ (True ∧ ((p3 ∨ p5) ∧ p1))))) ∨ p3) ∨ (True → ((p2 ∧ False) → (p2 ∧ ((False ∨ p5) ∧ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148696673738184511598054251423 : (((p2 → (((p3 → p1) ∨ p3) → (p3 → p1))) ∨ (p3 → ((((p2 ∧ p2) ∧ False) → (p4 → p3)) → False))) ∨ (p2 → ((False → p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65741341075350006413942780789 : ((p4 ∨ ((((p5 ∧ (((p1 ∧ (p2 → p1)) ∨ (p5 ∨ p2)) ∨ p3)) ∧ False) ∨ (p1 → (p3 ∨ (True ∨ True)))) ∨ (p1 ∧ (p4 ∧ True)))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55588004059902019859259332970 : (((p3 ∨ ((p2 ∧ p3) ∨ (p2 → p4))) → (((True → p3) ∧ ((p1 ∧ (p2 ∧ (((True → False) → False) → p4))) → (False ∨ False))) ∨ True)) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40167810005274031323305370175 : ((((((p5 ∧ ((p2 → (p5 ∧ p2)) → True)) → p2) → (((True ∨ ((p2 ∨ p2) ∧ p3)) ∧ p3) ∧ ((p4 ∧ True) → False))) ∧ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59793415299339795318397404595 : (((p2 ∧ p2) → (p5 ∨ (((True ∨ p2) ∨ p3) → (((False ∧ (p3 ∧ (p5 ∧ (True ∨ False)))) ∨ (((p1 ∨ p5) ∨ p4) ∧ False)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127780717283223327320083844137 : ((True → (((((p3 → p1) ∧ (p4 ∨ True)) ∧ ((p3 ∨ p3) → p3)) → p1) → ((p5 → p2) ∧ (p4 ∨ ((False ∧ p2) → p1))))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150163946485784357946796344054 : ((p1 → ((p5 ∨ (((True → p4) ∨ p2) → p5)) ∨ (False ∨ (((p3 ∧ p5) ∨ (False → p5)) → (p5 ∨ p1))))) ∨ (((p1 → True) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600562567825337074447479796639 : ((((True ∧ (p1 ∨ (((False ∨ (True ∧ p4)) ∨ p4) ∨ (False → ((p1 ∧ p1) → ((p5 ∨ p5) → (p3 → ((p2 ∨ True) ∧ True)))))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684484389119184318096695684190 : (((((False ∧ (((p4 ∧ False) ∧ p1) ∧ True)) ∧ ((p5 ∧ ((p5 → p5) ∧ (p4 → p2))) ∧ True)) ∨ ((p5 ∨ (p3 ∧ p2)) → (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111844630427267246413386938729 : (((((((False → p2) ∧ (False ∧ ((p5 → (True → (p2 → True))) → p4))) ∨ (p3 ∨ p2)) ∧ p3) → ((p1 → True) → False)) ∨ True) ∨ (p2 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113555635905199631825317559656 : ((((p3 ∧ True) ∧ ((((p5 → ((p3 → p2) ∧ p4)) ∨ ((False → (True → True)) ∨ False)) ∧ (p4 ∨ True)) → p5)) ∨ (p2 → True)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237992951508762265552496191754 : ((True ∨ p1) ∧ ((((((p5 ∧ p3) ∧ (p1 ∧ p3)) ∧ p5) ∧ ((p5 ∧ (((False ∧ (p2 ∨ True)) → p2) ∨ p2)) → (False → p2))) ∧ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40755491527559151286684577576 : (((((p2 → p4) ∧ (p3 ∧ (((p2 ∧ p1) → p4) → ((p3 → (((((p3 → p2) ∧ p1) ∨ False) → True) ∧ p4)) ∧ p5)))) → p4) ∨ False) ∨ p4) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ p1) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612649538277940028494513182536 : ((((((((p3 ∧ (p1 → (False ∧ p5))) → (p4 → (False ∧ False))) ∨ (True → (p3 ∨ p3))) ∨ (p3 → (p5 ∧ p2))) ∨ (False → p5)) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116152402491252165051363002302 : (((p1 ∨ (p1 → p2)) ∧ (((((((p5 → p5) → (False ∨ p1)) ∧ p2) ∧ p3) ∨ ((False ∧ p5) → p1)) ∧ p4) ∨ (p1 ∧ p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180723310279573770388792941332 : (((p3 ∨ ((p5 ∧ p5) ∧ p2)) ∧ (((p3 ∧ p2) ∨ (p3 → p2)) → True)) → ((p1 ∧ (p4 ∨ ((p3 → p2) ∨ (p2 ∧ True)))) ∨ (p1 → True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768946484182928746283100907990 : (((p5 ∧ (((p2 ∧ p2) ∧ (p1 → p4)) → (p4 ∧ ((((p1 ∧ p2) ∧ p4) ∨ False) ∨ (((p5 ∧ (p3 ∨ True)) ∧ (p1 ∧ p4)) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185237117277199397519419915423 : ((False ∧ (p1 ∧ ((p5 ∨ ((True ∨ p2) → p1)) → (True → False)))) ∨ ((((p5 → False) → ((p5 → (p2 → False)) ∨ p2)) → (p5 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119543826808710622981702023044 : ((p5 → ((p1 ∨ ((False ∧ ((True ∧ p3) ∧ ((False ∨ (p3 → p2)) ∨ (p1 ∨ p4)))) ∨ (p2 → (False ∨ p2)))) ∨ (False → False))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257986494432298880162750742004 : ((p4 ∨ p1) → ((((p4 → p4) ∧ p4) ∧ (True → ((True ∧ (p3 → ((p5 → (((False → False) ∧ p2) ∧ False)) ∧ False))) ∧ p2))) ∨ (p3 → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40623762217258798413685531989 : (((((p4 → (p5 ∧ (p4 ∨ (True → (((p5 → p4) → (p3 ∨ p5)) ∧ (p1 → (p1 ∧ (p3 ∨ (p1 ∧ p2))))))))) ∨ p5) → p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42163578834449691372820594313 : ((((p4 → True) → ((p5 ∨ (p4 ∧ ((p2 ∨ ((True ∨ ((p1 ∧ p2) ∧ True)) ∨ (((True ∧ p5) ∧ p4) ∧ True))) → False))) ∨ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202208623214756622772991834949 : (((True ∧ (p4 ∧ (p2 ∨ True))) → True) ∧ ((((p4 ∧ p1) → p2) ∨ p4) ∨ ((p3 ∧ (((p2 → p1) → (p4 ∧ (False → p2))) ∧ p4)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217625399422553286841354326141 : ((((False ∧ p3) → p1) → p2) → (((p1 ∧ ((((p1 → ((p3 → p1) → p2)) ∧ True) → False) ∧ p5)) ∨ (p3 → p2)) ∨ ((p2 ∧ p4) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ p3) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609663420136793816218389221439 : (((((False ∨ (p4 → ((p4 → (((p2 ∨ (p5 ∧ True)) ∨ p5) ∧ (p5 ∧ (p1 ∨ ((p4 → p4) ∨ (p1 ∨ True)))))) ∧ False))) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_115155822634478972421239035847 : (((p2 → ((((False ∨ (p1 ∧ p5)) ∧ p3) ∨ (p3 ∨ False)) ∧ p4)) → ((p3 ∧ ((True ∧ p4) ∨ (p2 ∨ (p3 → p5)))) ∧ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179094469034488979981119184786 : ((False ∧ (((((p2 → (p4 ∨ False)) ∨ True) → False) → (True → True)) → p3)) ∨ ((((p3 ∨ (False ∨ (p4 → (p2 → p3)))) ∧ p3) ∧ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44805537376605447912339831479 : (((((p4 → p1) → True) ∧ (False → ((((((p5 → (True ∨ False)) → p2) ∨ True) ∨ p2) ∧ (False ∧ (p1 ∧ (p2 ∨ p5)))) ∨ p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140193110382330905267745486984 : (((((p2 ∨ (p2 ∧ p1)) ∧ p3) ∨ ((((False ∧ True) ∧ ((p2 → True) → p2)) ∧ (False → p5)) ∧ False)) → (p1 → p3)) → ((p2 → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135666279968666924113348167052 : (((p4 ∧ (p4 → (True ∨ (p4 → ((p4 ∨ False) ∨ (True → ((True ∨ p1) ∨ True))))))) → (p1 ∧ ((p4 ∧ p2) → True))) ∨ (False → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113439683462953756274634640550 : (((((p5 → ((True ∨ (p3 ∨ True)) → (p3 ∨ False))) ∧ ((p3 → p2) ∧ (((p1 ∧ p3) → p2) ∧ p4))) ∨ p4) ∨ (False → p3)) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668864629938972152961845154270 : (((((((p5 ∧ True) → p1) ∨ (p4 ∧ ((p1 → False) ∧ ((p4 → p4) ∧ ((p3 ∧ (p2 ∨ p2)) ∨ p3))))) ∨ True) ∨ (p3 ∧ (False ∧ p1))) ∨ p1) ∧ True) := by
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



