variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39637942677253971880962461504 : (((p3 ∨ (((True ∧ True) → (p3 ∧ ((True → (((False ∧ ((True ∧ p5) → (p5 ∧ p1))) → p5) ∧ False)) ∨ (p5 → p1)))) → p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260910559148332589394934707791 : ((p4 → False) → ((((p5 → False) → (p2 ∨ True)) → (True ∧ (((True → p5) ∨ p5) ∧ p5))) ∨ ((((True ∧ p1) ∧ p1) ∨ (p2 → p4)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166161345291615226034031094282 : ((False ∧ ((((True → (p1 ∧ (p2 ∨ p3))) → p4) → p5) → ((p2 → p1) ∧ (True → p2)))) ∨ ((p5 → True) ∧ (p2 → ((p5 ∨ p1) → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66678930795028783706061557642 : ((True → (((p4 ∨ (p2 ∧ p5)) ∨ p3) ∨ ((((p1 → ((p2 → False) ∧ (True ∧ p4))) ∧ p5) → (p1 ∨ (False ∨ True))) ∧ (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206266700859074149107702951678 : ((False ∨ ((p1 ∧ p4) → (False ∨ p2))) ∨ (True ∧ (p1 → (p2 → ((((((p5 → p3) → p2) ∧ p5) ∨ (p3 ∨ p4)) ∧ (True ∧ p4)) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329642946225861775150739123589 : (True → ((p2 ∧ p1) → ((p4 ∧ p4) ∨ (((p4 → True) ∧ (False → True)) → (p3 ∨ ((((p3 → (p1 ∧ p4)) ∨ p3) ∨ p2) ∨ (False ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61907024268971856870578070437 : ((p2 ∧ (((p2 → (((p5 ∨ p5) ∧ (p1 → (((p4 ∧ p1) ∧ p5) ∧ ((p5 ∧ p5) ∨ True)))) → True)) ∧ False) ∧ ((False ∨ False) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614723523197589248044271626985 : ((((((False ∨ (p1 ∨ ((p3 ∨ (True ∨ (p2 ∧ (p3 ∨ True)))) ∨ (p1 ∨ p1)))) ∧ (p3 → False)) ∨ ((p5 → (p3 ∧ False)) ∨ p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_61441815037211004132850836163 : ((p1 ∧ ((False ∨ ((p5 → p2) ∧ (((((p5 ∧ p4) → p1) ∨ p3) ∧ ((p4 → p2) ∧ ((p1 → p5) ∧ (True → p2)))) → p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53908066897406949748303776910 : (((p5 ∧ ((True ∧ False) → ((p3 → (p5 ∨ False)) ∧ p1))) ∨ (((p1 → True) ∧ p1) → ((False ∧ (p5 → False)) ∧ (True ∧ (p1 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350915088436692053884024468207 : (p4 → (((((p2 → (((p4 ∨ (p4 ∧ p3)) ∧ (p5 ∨ (((p4 ∧ p4) ∧ p1) → (p3 → p5)))) → p3)) ∧ p4) ∨ True) ∨ p4) ∨ (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330511806340334021555372608330 : (True → (p4 ∨ ((p3 ∧ p1) ∨ (((p4 → p3) ∨ (p2 → ((((False → p5) ∧ (p1 → p5)) ∧ ((p1 → p1) ∨ False)) → p4))) ∨ (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105118778928452865877578398697 : (((((p1 ∨ ((p4 ∨ p5) ∨ ((((p2 ∨ (p2 → True)) ∧ p1) → p1) ∧ p5))) ∨ True) → (p4 ∧ p2)) ∨ ((False → p3) ∨ p1)) ∧ (False → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213824864743321730295082267498 : (((p4 ∧ (True → p4)) ∨ p4) ∨ (((p5 → (p1 ∧ p5)) → (((((False → p3) ∨ (p1 ∧ True)) ∧ p1) → p4) → (p3 ∨ (True ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246698853177610125077626643661 : ((p5 ∧ p4) ∨ ((((p5 → ((p1 ∨ p4) ∨ True)) → p1) ∨ ((p5 → ((p1 → True) → p5)) → p1)) → ((p3 ∨ p4) → (p5 ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (p5 → ((p1 ∨ p4) ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p5 → ((p1 → True) → p5)) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111707439482651228715503362764 : (((((((p4 → (p1 ∨ ((p1 → p4) ∨ (((p1 ∨ p5) → p1) ∧ p1)))) ∨ p1) → False) → ((p1 ∨ p3) ∧ p4)) → p1) ∨ True) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41449955877893797360054675870 : ((((((p3 ∧ p1) ∧ (p3 ∧ ((p3 ∧ (True ∧ p3)) → p5))) ∨ True) ∧ (True → ((p4 ∧ False) ∧ ((p1 → p3) → (p3 → p4))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677600944502460380281113381896 : ((((((p3 → (p5 ∨ (p4 ∧ ((p1 ∨ (p4 ∧ p1)) ∨ ((p2 ∨ (p4 → p5)) ∧ True))))) ∧ p1) → p3) ∨ (True → ((p4 ∧ False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611870482388697599953906385442 : (((((p4 → (p4 ∧ (p2 → ((((p5 → (p1 ∨ (False ∧ p2))) → p2) ∧ False) ∨ (p3 → ((p3 → (p2 → p1)) ∨ p5)))))) → p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_516518887846804112719632084594 : ((((p4 → False) ∨ (((p5 ∨ (p2 ∧ p5)) ∨ p3) ∨ (((((p5 ∧ p1) ∧ p5) ∧ p4) ∨ (((p4 → (False ∧ p3)) ∧ False) → p1)) ∨ p2))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147775949217795300183247635102 : ((((p4 ∨ p3) ∨ (((p1 ∧ p1) ∨ ((p5 ∨ p1) → (p5 → False))) → (True → ((p2 ∧ p4) ∧ False)))) → p5) ∨ (False → (p1 → (p5 → p2)))) := by
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
theorem thm_5_vars_160559678665374124627942941333 : ((((((True → (p2 ∨ p2)) → p2) ∨ ((False ∧ False) → p3)) → True) → (p2 ∧ ((p1 → p5) ∧ False))) → ((p1 ∧ (False ∧ (False ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → (p2 ∨ p2)) → p2) ∨ ((False ∧ False) → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231843825209943338215866939677 : (((p5 ∧ p3) → p1) → (((((p1 → False) → (((True ∧ True) ∧ p4) → p2)) ∨ False) ∨ (p2 ∨ (p5 ∨ ((p3 ∧ False) → (False → p2))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119364319817590214316400289547 : ((p3 → (p5 ∧ ((p4 ∨ (p1 → True)) → (((True ∨ (False → (((p1 → (True ∨ p4)) ∨ p3) ∨ p1))) → (p1 → p4)) → p1)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709098489387676937951100684174 : (((((p1 ∨ (p5 → p4)) ∨ ((p3 ∨ p2) ∨ True)) → ((p1 ∧ (p2 ∨ p4)) → ((p2 → p1) → ((False ∨ p1) ∨ (p3 → (p5 ∧ p1)))))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640044273830029619316540096259 : (((((p3 → (p4 ∧ p1)) ∨ ((p5 ∧ p4) ∧ ((((p3 ∨ (p3 ∨ ((p4 → p3) ∧ p3))) ∨ p3) ∧ (False ∨ (True ∨ p4))) ∨ p4))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354643749383251381107947666885 : (p5 → ((((p5 → (p1 → ((((True ∧ True) ∨ p2) ∨ (((p3 → p2) ∧ p2) ∧ (True ∨ False))) ∨ ((p4 ∧ p2) ∧ p5)))) ∨ p1) → p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336184271625701527888218395003 : (p1 → (((((p5 ∧ p5) ∨ (((p1 ∧ p2) ∨ p4) ∧ ((((p2 → (p2 ∨ True)) → False) ∧ (p3 ∨ True)) ∧ p3))) ∧ p2) ∧ (False ∧ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665919423952190809602798476726 : (((((((p2 ∨ (p4 ∧ False)) ∧ p4) → (p3 ∧ ((p3 ∧ p1) ∧ (((p5 → p2) ∨ False) ∨ (True → p2))))) → p1) ∧ ((p4 ∧ p5) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258309750599788848422900984733 : ((p5 ∨ True) → ((p5 ∨ (p1 → p3)) → ((p2 ∨ p4) ∨ ((((False ∧ (((p3 ∨ (p2 ∧ p3)) ∧ p5) ∨ (True → p2))) → p4) ∨ p4) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246376017320105976278661381675 : ((p5 ∧ True) ∨ (((True ∨ (p1 → (True ∧ (False ∧ (((p1 ∨ p1) ∨ p1) → p2))))) ∧ (p1 → (((False ∧ (p2 ∨ p4)) ∧ p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113019139960351788229990320104 : (((p5 ∧ (p5 ∧ (((p3 ∧ ((((p1 ∧ False) ∧ True) → p2) → p3)) ∨ (((False → True) ∧ p3) → (p1 ∨ p3))) ∨ p3))) → False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307200136776181033886114282461 : (p1 ∨ (p1 ∨ (((((((p3 ∧ (((p2 ∧ False) → p4) → p1)) ∧ p4) ∨ p5) → p5) ∨ True) → p4) ∨ ((((p3 ∨ p3) → p2) ∧ False) → p1)))) := by
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
theorem thm_5_vars_651538128595300740783087864766 : (((((True ∨ p2) ∧ (((p1 ∧ p2) → ((p3 ∧ ((((True → (True ∧ True)) ∧ p5) ∧ True) ∧ (True ∨ False))) ∨ p3)) ∨ p1)) ∧ (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305347170973869196794352394769 : (p1 ∨ (((False → p5) ∨ ((p5 → ((p2 ∨ (True → p3)) ∧ (True ∧ (p4 ∧ (p2 ∨ p3))))) ∨ False)) → (p4 ∨ (p4 ∨ ((p5 → p5) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48964867187805684415603943134 : ((((((((p3 ∨ (False → False)) ∧ ((((False ∨ p2) → True) ∧ p2) → False)) → p3) ∧ (p2 ∨ True)) ∨ p1) ∨ p5) ∨ ((False ∧ p5) → p5)) ∨ p4) := by
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
theorem thm_5_vars_1172871032408200610420428181 : (((p3 → (False ∨ True)) ∧ (((True → p4) ∨ (p2 ∨ True)) → ((False ∨ ((p2 ∨ True) ∨ True)) → ((False ∧ p5) ∧ (p2 ∨ True))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → p4) ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ ((p2 ∨ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51356262101407923676101163600 : (((((((p5 → p4) ∧ ((p3 ∧ (p5 → False)) → p3)) ∨ p2) ∨ (p3 ∧ (p3 ∧ p1))) ∧ p2) → ((p4 ∧ False) ∨ (p2 ∨ (p5 ∨ False)))) ∨ p3) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119338342923953118174853172675 : ((p3 → (((p1 ∧ (False ∨ p4)) → p1) → (p4 ∨ (p1 → (((p1 ∨ ((p5 ∨ True) → (p1 ∧ (p5 ∨ p5)))) ∧ p5) ∨ p5))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343023960453118793305819205133 : (p2 → (((p4 → (True ∧ p2)) ∨ p2) → ((((p1 ∨ False) ∧ ((False ∧ True) → ((p2 ∨ False) ∨ ((p2 → p1) ∧ True)))) ∨ p3) ∨ (p2 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227878917455929541732453992529 : ((p2 ∧ (p5 ∨ False)) ∨ ((((False ∧ (p5 → (False ∨ False))) ∨ (p4 ∧ (p4 ∨ (False ∨ p4)))) → (p3 ∨ (p3 ∧ p1))) ∨ (False → (False → p3)))) := by
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
theorem thm_5_vars_138802445291699018097801358805 : (((True ∧ (((False ∨ ((p4 ∧ p5) ∧ ((p3 → (False → (p5 ∨ p2))) → (p5 ∧ p3)))) → (False ∧ p1)) ∨ False)) ∧ p3) → ((p2 → p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681938624332151643555732074714 : ((((((((p2 ∧ (((p1 ∧ False) ∧ (p1 → p1)) ∨ True)) → (p3 ∨ p5)) → p2) → p4) ∨ p2) ∧ (p5 ∨ (p5 → ((p1 → p2) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114242491847868534743849832792 : (((p1 ∨ (p4 ∧ (p1 → (p4 → (((((p1 → True) ∨ True) → p4) ∧ True) → (p5 ∧ (p3 ∨ p4))))))) → (p1 ∨ (p5 → p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245587827787626450083393473363 : ((p3 ∧ False) ∨ (((p4 ∧ p5) → ((False ∧ p1) ∨ ((p4 → (True ∨ ((True → ((p4 ∨ False) → p5)) → p5))) ∧ ((p2 → False) ∨ p4)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194017350328025415656885933660 : ((p4 ∨ ((p2 ∧ p3) ∨ ((p3 ∧ (p4 ∨ p2)) ∧ p1))) → ((p2 ∨ (p1 ∨ (p5 ∧ p2))) ∨ (False → ((p1 ∨ (True ∧ p3)) → (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316742127689219866536789861027 : (p3 ∨ (True → (((p4 → (((p4 ∧ False) ∨ ((p1 → p5) ∧ (p5 ∧ p5))) ∧ ((True → p4) ∨ p5))) ∧ (p3 ∧ (p1 ∨ p1))) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_112944991186002185806173123838 : (((True ∧ ((p2 ∧ (p5 ∨ ((p5 ∧ (p4 ∧ ((p2 ∧ (p1 ∨ ((False ∧ (p3 ∧ p5)) → p5))) → False))) → p3))) ∧ p2)) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593920020353712754985477698553 : ((((((p4 ∧ ((True → p1) ∨ (True ∨ ((p5 ∨ False) ∨ p1)))) ∧ (((p2 ∨ p2) ∧ p2) → p5)) ∨ ((p2 ∧ p5) ∧ (p1 → p3))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58188790509141863275681634581 : (((p3 ∧ p4) ∧ (((p4 → (False → p4)) ∧ (False ∨ p3)) ∧ (False ∨ (((False → (p1 ∨ p1)) ∧ True) ∧ (p2 ∨ ((p4 → p5) ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136068142057747340522529163196 : ((((p4 ∧ (True → p2)) ∨ (True → (p4 → p3))) ∧ (p4 ∧ ((p4 → (((True ∧ p5) ∧ (True ∨ p2)) → p5)) → p4))) ∨ (True ∨ (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171831005840431928593494065132 : ((((p5 ∨ (p1 ∨ True)) ∧ (((((p2 → p2) ∨ p3) ∧ p2) ∧ p1) ∨ p5)) → p1) ∨ (((True ∧ p4) ∨ ((p1 → p3) ∨ p2)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319455359883921896683407685772 : (p4 ∨ ((((p2 → ((False ∧ p2) ∧ (p2 ∧ True))) → p2) ∨ (p1 ∧ p3)) ∨ ((p4 ∧ p5) → ((((p3 → p5) ∧ (p4 → p2)) ∧ False) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_677556982220430000763102984039 : (((((p5 ∨ (((p2 → p3) → (((True → p1) ∨ p1) ∨ ((True ∨ p3) ∧ (True → True)))) ∨ p5)) ∨ p2) ∨ (p2 ∧ ((True → p2) ∨ p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218960252928097275460905930196 : ((p4 ∧ ((p5 ∨ p4) ∧ p2)) → ((((True ∨ False) → p5) → (((p2 ∧ ((False → (p5 ∨ p4)) ∨ False)) ∨ p5) → p1)) ∨ (p4 ∨ (p1 → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66791097918295151456487214475 : ((True → (p1 ∨ (((p3 ∧ False) ∨ ((((((p4 ∨ (True → (p2 ∧ p1))) → p2) → (p1 ∧ p5)) ∨ p4) ∧ p1) ∧ p5)) → (p4 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249110458655125583328228129441 : ((p4 ∨ p2) ∨ ((p1 ∧ ((p4 ∨ True) → ((((False ∨ p5) ∨ (p4 ∧ p1)) → ((p2 → p5) ∨ False)) ∨ (p4 → ((True → p3) ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734847649071446152454719709867 : ((((p2 ∨ p2) ∧ ((((False → (p1 ∧ p4)) ∨ p3) ∧ ((p1 → ((p4 → (p3 → (p2 ∧ p2))) → p1)) ∧ ((False ∨ p5) → p1))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68297919028536741526875717461 : ((p3 → (((p3 ∨ ((((((p1 → p2) ∨ (p3 ∧ True)) ∨ p3) ∧ p4) → p3) ∧ p2)) ∧ (True ∨ (p2 → p4))) → ((p3 → p1) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228736636333479496902475145266 : ((p2 ∨ (p3 → p4)) ∨ ((((p5 ∧ (p3 → (False → (False ∧ p1)))) → (p1 ∧ ((p4 ∨ (p4 → (False ∨ p5))) → p3))) ∧ (p3 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165381641797389992055202287537 : ((((p5 → ((p1 ∧ p2) → (p1 → p1))) → ((p1 → p5) ∧ False)) ∨ ((False ∧ False) ∨ p4)) ∨ (((False → False) ∧ False) ∨ ((p4 → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807173798492556552333650187184 : (((p4 → ((((((((False ∨ p2) ∨ p1) → p1) ∨ p3) → p1) ∨ (p1 → (p4 ∨ False))) ∨ True) ∨ ((True ∨ (p1 ∧ True)) ∧ (p3 ∨ p1)))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_56715861292793614478236475484 : ((((True ∨ p1) ∨ p4) ∧ (p1 ∨ (((p5 → ((p1 ∨ False) ∨ True)) ∧ (p3 ∧ ((False ∨ True) ∨ p2))) ∨ (p1 ∨ ((p2 ∨ p5) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788518256948337287600282687584 : (((p5 ∨ ((p1 ∨ (False ∨ ((p1 ∨ True) ∧ ((p1 ∧ ((p5 ∧ p4) → (p1 ∨ (p4 ∨ p4)))) ∨ (p2 → (True ∨ (False ∨ False))))))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_773498594797475682480651379143 : (((False ∨ ((((p5 ∧ ((((((True → p1) ∧ p1) ∧ p4) ∧ ((p4 ∧ False) → True)) ∧ p2) ∨ (p3 → True))) → p2) → (p5 ∨ p1)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_122401839205686298072520526198 : ((((((True → ((True → False) → p5)) → (True ∨ (((p2 → p3) → p1) ∨ p3))) ∨ (p1 ∨ True)) ∧ (p2 ∨ p3)) ∨ (p3 ∨ p1)) → (False ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53680777045928767760917651739 : (((False ∧ ((p2 ∨ ((False ∨ False) ∨ (p3 → p4))) ∨ p2)) ∧ (p1 ∧ ((p2 → (p2 ∧ False)) ∧ ((p2 ∨ p5) → (False ∧ (p2 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40536207823334906282650916745 : ((((p3 ∨ ((((p5 → p2) ∨ False) ∧ (((p3 ∨ (p1 → ((p1 ∨ p4) ∨ (p2 ∧ p5)))) ∧ (p3 ∧ True)) → p4)) ∧ p5)) ∨ p5) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199042396393454410738137718636 : (((((p4 ∨ (p5 ∧ p1)) → p1) ∨ p2) ∧ p2) → (((p4 → False) → p3) → (((p3 → p1) ∨ (((p2 ∨ p3) → (p5 ∧ p3)) → p5)) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p2 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166171246444320520393334547833 : ((False ∧ (p3 ∧ (p4 ∨ ((p5 ∨ True) ∧ (p4 ∨ (((False → (p1 ∧ p4)) ∧ p3) → p4)))))) ∨ (p5 → ((p4 → (p2 → p5)) → (p4 → True)))) := by
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
theorem thm_5_vars_798981294686073032139106403595 : (((p1 → ((p5 ∨ p5) ∨ ((((False ∨ (p3 ∨ ((p4 ∧ (True ∨ False)) ∨ p4))) ∨ (((p3 ∨ False) → True) ∨ (p4 ∧ p5))) ∧ p4) ∨ p1))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201971842965499966625296477160 : (((False → ((False → False) ∧ p1)) ∨ True) ∧ ((((((p2 ∧ (p2 → (True → (False ∧ p1)))) → p3) → (False ∨ p4)) ∨ p3) ∧ (True → p4)) ∨ True)) := by
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
theorem thm_5_vars_797375754766335710387648354170 : (((p1 → ((((p3 → p5) ∧ p1) ∧ ((((p4 ∧ p4) ∧ ((p5 ∨ (p5 ∧ p1)) → ((p2 ∨ p2) → p2))) ∨ (p2 ∧ p4)) ∧ p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143849041249792589844442864639 : ((((p4 → ((False ∧ p3) ∧ (p3 ∧ (p4 ∨ (p3 ∧ ((((p4 ∨ p1) ∨ True) ∧ p3) ∨ p4)))))) → p5) ∨ True) ∧ ((True ∨ p3) ∧ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302639744758877681303733969108 : (False ∨ (p2 ∨ ((((((True ∨ p2) ∧ (p4 ∨ False)) ∨ (True ∨ (p5 ∧ p1))) ∧ p5) → False) → (((False ∨ p5) → ((p2 → p4) ∨ p2)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((((True ∨ p2) ∧ (p4 ∨ False)) ∨ (True ∨ (p5 ∧ p1))) ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260541146760952104689226336244 : ((p3 → p1) → ((((((p4 ∨ (p5 ∨ p5)) ∧ (p4 ∨ (True → ((p2 ∨ p3) ∧ (p4 → p4))))) ∨ p2) ∨ p1) ∧ p2) → (False ∨ (True ∧ p2)))) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h4
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172473708529842187931165340545 : (((((p4 → True) ∨ p1) ∨ False) → ((True → (((p1 → p1) ∧ p3) ∧ p2)) ∨ p2)) ∨ ((p4 → p4) ∨ (((p2 ∨ p2) → p5) ∧ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358065314892075800673738881245 : (p5 → (p1 ∨ (((True ∨ p4) ∨ p3) → (((False ∨ (p1 ∨ p3)) ∨ ((p2 ∧ (p1 ∧ False)) → ((p1 ∧ p4) → (p4 ∨ (p4 ∨ p3))))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340810523506169554116483193465 : (p2 → (((((p4 ∨ p1) ∧ ((((p4 → (True → p4)) ∧ (p3 ∨ p1)) → ((p2 ∧ p1) ∨ p3)) → True)) → (False ∨ p1)) ∧ (p2 ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197702891664172040525540915411 : (((p1 → (p2 → (p3 ∨ p4))) → (False ∨ p2)) ∨ (((True → p3) ∧ ((p3 ∧ (False → (p4 ∨ p3))) ∧ (p1 ∨ (p3 → (p5 → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327790428156766823935298199028 : (True → (((((p5 ∨ (p4 ∨ True)) → ((((p1 → p1) ∨ False) ∨ p4) → ((p5 ∨ p3) → (True → (p1 ∧ p2))))) → p1) ∧ p3) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173365158525869916978495624315 : ((p3 → ((p4 ∨ True) → (p3 ∧ ((False ∨ False) ∨ (p3 → ((p2 ∨ True) → p2)))))) ∨ ((False → p4) ∧ (p2 → ((p1 ∨ (True ∧ p1)) → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314838273291335671386672040391 : (p3 ∨ ((((False ∧ False) ∨ p5) ∨ ((p2 → (p3 → p4)) ∨ (False ∧ p5))) ∨ ((((False ∨ False) ∧ (False → (p3 ∨ (p3 ∧ True)))) ∨ p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179419433254118029581500039209 : ((p4 ∨ ((((p2 → p3) ∨ (p1 ∧ p3)) → (True → p4)) ∨ (p5 → p3))) ∨ (((((True → p2) → p3) ∧ p3) ∨ p3) → (True → (True ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678297449772509322907134097114 : (((((p4 ∨ ((p5 → (p3 ∨ True)) ∧ (p3 → p5))) ∨ ((p5 → ((p3 → p1) → (False ∧ p2))) → False)) ∨ ((p4 → p3) ∨ (p3 → p3))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398470886367838009462496121929 : ((((p5 ∨ (p1 → ((p5 ∨ (False ∨ (p4 ∧ ((p1 ∨ (True ∨ p2)) ∧ p2)))) ∨ (p3 ∨ (p1 ∨ (p2 ∧ ((p1 ∨ p1) → False))))))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264969005522920832792306428806 : (True ∧ ((p4 ∨ True) → (((p4 ∨ p2) → ((False ∨ p1) → ((((p2 ∧ p1) → p3) → (False ∧ ((p5 ∨ True) → p2))) ∨ p2))) ∨ (True ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65008651283224798450604788716 : ((p2 ∨ ((p5 ∧ p5) ∧ ((((True ∨ False) ∨ (p2 ∨ ((p4 → p1) ∧ ((False → p1) → (True → False))))) ∨ p5) ∧ ((p1 ∧ p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186336154943411526277473581547 : ((((((p2 ∨ p5) ∧ p2) ∨ False) → (p4 → (p2 ∧ True))) → p4) → ((p2 → ((((p2 → True) ∨ p3) ∨ (p3 ∧ (p3 → True))) ∧ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ p5) ∧ p2) ∨ False) → (p4 → (p2 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114309553471014612138788473596 : ((((((p1 ∨ False) ∧ False) ∧ (False ∨ False)) ∧ (((p5 → p4) ∨ (p2 → (True ∧ False))) ∧ True)) ∧ ((p1 ∨ (False ∨ p1)) → p5)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265004976308925494095133975226 : (True ∧ ((p3 → p2) → (((((False ∨ True) → (((True ∧ False) ∧ ((((True → p1) ∨ p4) → (p2 → p5)) ∧ p3)) ∧ p4)) ∨ True) ∨ p1) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173190300090492844930288398932 : ((p4 ∨ (p3 ∨ (((((p5 ∨ False) ∧ p3) ∧ (p2 ∨ p5)) ∧ (p4 ∧ p1)) ∨ p4))) ∨ (p1 → (((p5 → p5) ∧ ((False ∧ p2) → False)) → p1))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54670042022865675150001863004 : ((((((p2 ∨ False) ∧ (p1 ∧ p1)) ∧ False) → p4) → ((True ∧ (False ∨ p2)) ∧ ((p4 ∧ p2) ∧ ((p5 ∧ ((p3 ∨ False) → True)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49462911419088417061115813817 : ((((False → (False ∨ (((False ∨ (p2 ∧ ((True → p5) ∧ (False → (p2 ∧ (p5 → p2)))))) ∧ p3) ∨ p2))) ∨ p4) → (p1 ∧ (False → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147700018333378778351449258838 : (((((p2 ∧ (p3 ∨ (((p1 → p4) ∨ p5) → (p3 ∨ p3)))) ∨ p1) → (p1 ∨ (False ∨ (p2 ∨ p4)))) → p5) ∨ ((False ∨ False) → (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_165808737594085509052940961703 : ((((True ∨ p4) → p3) ∧ (((p3 → ((False ∧ (p5 ∧ p3)) ∧ True)) ∧ p2) ∧ (p1 ∨ p2))) ∨ ((False ∨ (((p4 ∧ p4) ∧ p1) ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247607048150398010548150630275 : ((False ∨ p5) ∨ (((p3 ∨ p4) → ((((p4 ∧ ((p1 ∨ p4) ∨ p2)) → (False ∨ False)) → p5) ∨ (True → p3))) ∧ ((False ∧ (p3 ∧ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∧ ((p1 ∨ p4) ∨ p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313973399081201124643275066337 : (p3 ∨ ((((((p5 ∨ p4) → (p5 ∧ p1)) → ((p3 → p3) ∧ p5)) ∧ p5) ∧ (((p2 → ((p5 → p4) ∨ p5)) ∧ p4) ∧ p1)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181417245259480977235710564143 : ((p2 ∨ ((p4 ∨ p5) ∨ ((p1 ∧ (p5 ∨ (p3 → p1))) ∧ (p5 ∨ p4)))) → ((True ∧ (((p3 → False) ∧ p4) ∨ False)) ∨ ((p3 → p3) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
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
        exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115713550022646810921172102253 : (((((p1 → p2) ∧ (p3 ∧ p5)) ∨ False) → (p1 ∨ (p4 ∨ ((p1 → (False ∧ True)) ∨ ((p1 ∨ False) ∧ ((p1 → p3) ∨ True)))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



