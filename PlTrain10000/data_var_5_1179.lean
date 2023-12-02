variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649626848342399111603867775082 : ((((((p1 ∨ (((p5 ∨ (p2 → p3)) ∨ p1) ∨ p1)) → (p3 ∨ ((p3 → True) → (p2 → (p1 ∨ False))))) ∨ (p3 → True)) ∧ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115983002036075389057459105861 : ((((p3 ∧ (p2 ∧ p3)) ∨ p1) → (((False ∧ ((p1 → p5) → False)) ∨ ((p5 ∧ p3) ∨ p2)) ∨ ((True → True) ∨ (p2 ∧ False)))) ∨ (p4 ∧ False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207341527618673427946876513777 : ((((p4 ∨ p3) ∨ (p1 ∨ p2)) ∨ True) → (((((p5 ∨ p2) → (((False ∧ True) ∨ (p2 → (p3 ∧ p3))) ∧ p3)) ∨ p4) ∧ p4) → (p5 ∨ p4))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149295647242966556669433124929 : (((p5 → p2) ∨ ((((p2 ∨ False) ∧ p5) ∧ (((True ∧ p3) ∧ (False ∨ (p3 ∧ True))) ∧ p3)) ∧ (p4 ∧ False))) ∨ (((False → False) ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756469901515183133396023536659 : (((p1 ∧ ((((((p5 → p3) → (((p1 → False) ∧ (True ∧ False)) → True)) → (p4 → False)) ∧ p1) → False) ∧ (((p1 ∧ p5) → False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311060824918271676659346731481 : (p2 ∨ ((False ∨ p1) ∨ (True ∧ ((((((p5 ∧ (False ∨ (False ∨ (p5 ∨ False)))) ∨ ((p4 ∧ (p5 → p3)) ∨ p5)) ∧ True) ∨ p3) ∧ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_38087165375031393339901253785 : ((((p3 ∧ (True ∨ (((p1 ∧ True) → ((p3 ∧ p3) ∨ p2)) ∧ (((p2 ∧ p5) → p2) ∨ ((p2 ∨ p3) ∧ False))))) → (p3 ∧ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124638977983142930268940975813 : (((((False → (p5 ∧ p5)) ∨ p2) ∨ True) → (((p2 ∨ ((((True ∧ p5) ∧ (p5 ∧ True)) ∧ p3) ∧ (p2 → p1))) → p4) ∨ True)) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141957956943484485757855161138 : (((True ∨ p4) → ((((False ∨ p5) ∨ ((p2 ∧ False) ∨ ((p1 → p2) → (p2 ∧ (p2 ∧ p5))))) ∨ p4) ∧ (False ∧ p3))) → ((True → p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147785995866948799840312009019 : ((((False → True) → ((p4 ∧ (p1 ∧ ((p1 ∧ (True ∨ p3)) ∨ (p3 ∨ ((True → p1) → p2))))) → p1)) → p3) ∨ (((p2 ∨ p2) ∨ p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767760821680627279219491955038 : (((p5 ∧ ((((((p4 → False) ∨ (p5 ∨ (p1 ∨ p1))) ∧ (((p4 ∧ p2) ∨ ((False → p4) ∨ (p1 ∨ p1))) ∨ p3)) → p5) ∨ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218806829707536094720534916308 : ((p1 ∧ (p4 ∨ (p2 ∧ False))) → (((((((True → (p2 ∨ p1)) ∧ (True ∧ p3)) → False) ∧ (p1 → True)) ∧ ((p1 → False) ∨ p5)) ∧ p3) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305401892079101799644008554249 : (p1 ∨ ((((p5 ∧ p2) ∧ (p1 ∨ ((((p3 ∧ p4) → p4) ∨ p3) → p1))) ∧ (False ∨ p1)) ∨ (p2 → (False → ((True → True) ∧ (p5 → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148993289448244339782356921948 : (((p5 ∨ (p3 ∨ True)) ∧ (((True → (((p4 → p2) → (p4 → (p3 → (p4 → False)))) ∧ p3)) ∧ p2) → p3)) ∨ ((p1 ∧ p2) ∨ (False ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135371066936718048590457584876 : ((((False ∧ (((p4 ∧ True) ∧ (False → (False ∨ ((True ∨ (False → p5)) ∧ True)))) ∨ p3)) ∧ p3) ∨ ((True ∧ p2) ∧ True)) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215993622674531167590670559983 : ((p4 ∨ (p2 ∨ (False ∨ False))) ∨ ((True → ((((p3 → p2) ∧ (p4 → p3)) ∨ ((p1 ∧ p1) → ((p3 → (p2 ∧ p2)) → p3))) ∧ p3)) → p3)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49823284309053948940453247442 : (((p3 → ((((p2 → (p4 ∧ p5)) ∧ (p1 ∧ p3)) ∨ (p4 ∧ ((p3 → p1) → (p3 ∨ (False ∨ False))))) ∧ p2)) → ((p4 ∧ p1) → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157353272021291223818794677510 : (((True → ((p4 ∧ (p3 → p2)) ∨ (((p3 ∨ ((False ∧ p4) → p5)) ∨ (p4 → p5)) → p1))) → p3) ∨ (True ∨ ((True ∧ p4) → (p1 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172386365293937742655450450541 : (((((False ∨ p4) ∨ (p5 ∨ p5)) → p5) → (((p3 ∨ False) → p2) ∧ (True ∧ p1))) ∨ ((False → (p1 → ((False → p5) ∧ (p2 → False)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149581781391474025746868674112 : ((p3 ∧ ((p3 ∧ (p4 ∨ ((p2 → ((p5 ∧ (p4 ∧ ((p1 ∧ p3) → (p3 → p2)))) → p3)) → p4))) ∧ p2)) ∨ ((p1 ∨ True) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146977745130356327178987843400 : ((((((True ∧ (True ∨ ((p2 ∨ p1) ∨ p5))) → p5) ∧ (((p4 → p1) → p4) ∨ (True ∨ p5))) → p1) ∧ False) ∨ ((p2 ∨ p4) → (p4 ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194712175883196278600761554991 : ((((True ∨ p4) → ((p3 ∧ p4) → True)) ∨ True) ∧ ((p1 ∧ (True ∨ (p5 ∨ (p1 ∨ True)))) → (True ∧ ((p5 ∨ (p2 ∨ (p2 → p1))) ∧ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260111502470797189837052626815 : ((p2 → p1) → ((((p1 → p2) → (p5 → (p4 ∨ ((True → (((p1 ∨ (False → p4)) ∨ (p3 ∧ p2)) → p2)) ∧ p1)))) → p2) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166429589630616677537092840696 : ((p1 ∨ (False ∧ (p3 → (((p3 ∨ (p1 → (p3 → p1))) → True) ∨ ((p2 ∨ p4) ∧ p1))))) ∨ (p3 ∨ (((p2 ∨ (p1 ∧ p4)) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307699996235903551093919484732 : (p1 ∨ (p2 → ((False ∧ p1) ∨ (((p1 ∧ (p1 → p2)) ∨ p5) ∨ (((p3 ∧ (True ∨ (p4 ∨ p3))) ∨ ((p4 ∨ (p2 → p2)) ∨ True)) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122060320579134568132498480754 : (((p2 → ((((p1 ∧ (((p1 → (p2 ∧ False)) → p5) ∨ (p5 ∧ True))) → p4) → (((p5 ∨ False) ∨ True) → p3)) ∨ p2)) → False) → (p4 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((((p1 ∧ (((p1 → (p2 ∧ False)) → p5) ∨ (p5 ∧ True))) → p4) → (((p5 ∨ False) ∨ True) → p3)) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215983921945920036616754601136 : ((p4 ∨ (p3 ∧ (p3 ∧ p4))) ∨ (((p4 ∧ (p4 → False)) ∨ p2) ∨ ((p3 ∨ (p3 → True)) ∨ ((p5 ∨ p3) → ((True → (p2 ∧ p1)) ∨ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249500641070898331086402851310 : ((p5 ∨ p1) ∨ ((False ∨ ((False ∨ p2) → p5)) ∨ (p3 ∨ (True → (((p2 ∨ (p1 ∨ p1)) → p3) → (p1 ∨ (p5 ∨ ((False ∧ p5) → False)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_609068338643676869160745837750 : (((((((p1 ∧ (p5 → (p1 ∧ p1))) ∨ (p5 → p3)) → ((((p2 ∨ p4) ∧ (p3 → (p2 → p2))) → (p1 ∨ p4)) → p2)) ∨ True) ∨ p1) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_4010392005108462732668683345 : (p1 ∨ (p5 ∨ (((False → ((False ∨ ((False ∧ True) → p4)) → (((p3 ∧ p4) ∨ True) ∨ (False ∨ True)))) → (p1 ∨ p4)) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_180570542756878833616685150877 : ((((p2 ∨ (p4 → (p1 ∨ p3))) ∧ (False ∨ False)) → ((p3 ∧ p4) ∧ p2)) → (((True ∨ (p5 ∧ True)) ∨ p1) → (((p3 → False) ∨ True) ∨ p3))) := by
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
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114541629079997020890634085718 : (((p5 → (((((p2 ∨ (((p4 ∨ (p1 → p3)) ∧ p2) ∨ False)) ∧ True) ∨ False) → True) ∨ p1)) → ((p4 ∨ True) ∧ (p5 ∧ p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302729454824810819033541956605 : (False ∨ (p3 ∨ (p2 → (((p2 ∧ ((p3 ∨ (p2 → ((p5 ∨ ((p3 → False) ∧ p4)) ∧ p3))) ∧ p2)) ∧ ((p1 → p3) → (p5 ∨ False))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860113992736499979274250837040 : (((((((True ∨ (p4 ∨ p1)) ∧ p2) → ((False ∨ ((p2 → p4) → p5)) ∨ (p1 → (((p4 → p5) → False) ∧ p3)))) ∨ (True ∨ True)) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ (p4 ∨ p1)) ∧ p2) → ((False ∨ ((p2 → p4) → p5)) ∨ (p1 → (((p4 → p5) → False) ∧ p3)))) ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789237235751967099799384515819 : (((p5 ∨ (((p5 → (p3 ∨ (((p1 ∨ p4) → False) → (p1 ∧ ((p1 ∧ p4) ∨ (True ∧ p1)))))) → p5) ∨ (p5 ∨ ((p5 ∧ p2) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756696962034261479813419883731 : (((p1 ∧ ((p4 ∨ ((((((p4 → p3) → p3) ∧ False) ∧ p5) ∧ (p2 ∨ p3)) ∨ p1)) → (p4 → (p5 ∨ ((p2 ∨ p3) ∨ (p1 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202915374162720641843824361945 : (((p1 ∨ True) ∨ (p2 ∧ (p5 ∨ p1))) ∧ (p5 ∨ (p3 ∨ ((((p4 ∧ (p1 ∨ p4)) → ((False ∧ p3) → True)) ∨ p2) → ((p1 ∧ p4) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256685820183447948324902538014 : ((p1 ∨ False) → (p5 ∨ ((p4 → ((p1 → p2) ∨ (p5 → p4))) → (p2 ∨ ((p5 ∧ p3) ∨ (p1 ∨ (((p5 ∨ p5) → (True ∧ p5)) ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325824902085733140513045084798 : (p5 ∨ (p3 ∨ ((p4 ∧ (True ∧ p5)) ∨ (((False → ((True ∧ ((p3 ∧ (p2 → True)) ∨ (False ∧ p3))) ∧ (p3 → False))) ∧ False) ∨ (p5 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198244708958130805079139344510 : ((True ∧ (p1 ∨ ((p2 ∧ (p2 ∨ p4)) → False))) ∨ (False ∨ ((p4 ∨ ((p5 → p1) → (p3 ∨ p3))) ∨ (True ∨ (((False ∨ p1) ∧ p2) ∧ True))))) := by
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
theorem thm_5_vars_301067838507801543179057527695 : (False ∨ ((p5 ∨ ((((False ∧ (p1 ∨ p1)) ∧ p2) ∨ True) ∨ True)) ∨ ((p2 → (p5 ∨ (((p2 → p3) ∧ p2) ∧ (p4 → p4)))) ∧ (p1 ∧ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149678181594360725672020488740 : ((p5 ∧ ((((False ∨ ((p5 ∨ p5) → ((p5 ∨ p5) → True))) → p3) ∨ (((p3 ∨ p1) ∧ p1) ∧ p4)) ∨ True)) ∨ ((p2 ∧ False) → (p3 → p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152657371424891134417938584130 : (((p1 → p4) ∧ ((False ∨ (((p3 → (p4 ∨ ((p2 → True) ∧ p2))) ∨ (p4 ∧ p3)) ∨ (True ∨ p2))) → p5)) → (p5 ∨ ((p5 ∧ p3) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (((p3 → (p4 ∨ ((p2 → True) ∧ p2))) ∨ (p4 ∧ p3)) ∨ (True ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225307383463651578757630992036 : (((False ∨ p2) ∧ p5) ∨ ((True → (True ∧ (p2 ∨ ((((p4 ∨ ((p3 ∧ ((p5 ∨ p1) → False)) → p3)) → p3) → p4) ∧ (False ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65121826186554872516784437253 : ((p2 ∨ (True → (p4 ∨ (p3 ∨ (((p4 → (p5 → ((((p1 ∧ (p4 ∨ p3)) ∨ (True ∨ p1)) ∧ p3) ∨ True))) → p1) ∧ (False → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4179074063655138418704090602 : (p4 ∨ ((p3 ∧ p2) ∨ (((p1 → p4) → False) → ((((p4 → p1) ∨ p3) ∧ p5) → ((False ∧ (p3 ∧ p2)) ∨ (p1 ∨ (False → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233828813959229576274631394786 : ((p4 ∨ (True ∧ p1)) → ((p2 ∨ (((False ∧ p2) ∨ (((p1 → (False → p3)) ∨ ((p2 ∨ False) ∧ (False ∨ True))) → (p5 → p5))) ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200469453983933158728344322017 : (((p4 → p2) ∨ (p2 ∧ ((p5 ∨ p3) ∧ p2))) → ((p5 → (((((p3 ∧ p3) → ((True ∧ p4) ∨ (p3 ∧ True))) ∧ p1) → True) → p3)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
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
theorem thm_5_vars_134578404339985225091451397087 : ((((p2 → (((p3 → p4) → (((p5 → p4) ∨ (p4 → p5)) ∧ (p4 → p3))) ∨ (False → False))) ∧ (p1 → p1)) → p1) ∨ ((True ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46886007228939135611350728459 : ((((((((p3 ∨ p3) ∧ p5) → ((((True ∧ (p5 ∧ p1)) ∧ p3) ∨ True) ∧ ((True ∧ p3) ∧ p1))) → p3) ∨ p2) ∨ p2) ∨ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51119593049058004843932367281 : (((((((False ∧ p4) → p4) → (p5 ∧ ((p4 → p5) ∨ True))) ∧ ((p5 → p1) ∧ p5)) ∨ False) ∨ (False → ((False ∧ (p1 ∨ True)) → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661802024350200354205381026426 : (((((True ∨ ((p3 ∨ (p5 ∨ (p2 ∧ (p4 → (p2 ∨ False))))) ∨ ((False ∨ False) → p5))) ∨ ((p4 → (p3 ∨ p2)) ∨ p4)) → (p1 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232321280189404369555276893061 : (((p3 → p4) → False) → ((p2 → ((p1 ∨ (p2 → (p2 ∧ (p3 → p1)))) ∧ False)) ∨ ((p1 → ((False ∧ p3) ∧ p2)) ∨ (p5 → (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195829596644982287093654929422 : (((True → False) → (((True → p1) ∧ p4) ∨ p5)) ∧ (((p5 ∨ p2) ∨ ((((p3 ∧ p3) ∧ (p2 → False)) ∨ (p1 ∧ p1)) ∨ True)) ∧ (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233174695296603267090311781915 : ((p5 ∧ (p1 ∨ p5)) → (p4 ∨ ((False ∨ (((p4 ∨ (p5 → p3)) ∧ (False → True)) ∨ p5)) ∧ ((((False ∨ True) → (True ∨ False)) → False) → p1)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((False ∨ True) → (True ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h8
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299286431426193542881618483380 : (False ∨ ((((False ∨ (p5 ∨ p4)) → ((p4 → ((p5 → p2) → p3)) ∧ p2)) ∧ (p3 ∨ (p5 → (p1 ∨ (p1 ∧ (p3 → (False ∨ p5))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129098003597036649666343166958 : ((((p1 → (False ∨ (((((p5 ∧ (p5 ∧ (p2 ∧ p2))) ∧ (p1 → (p3 ∧ True))) ∨ p3) → p5) → False))) ∨ True) ∨ p5) ∧ (True ∨ (p5 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692450110450178987170641599775 : ((((((p5 ∨ ((p4 → p5) ∨ p5)) ∧ ((p4 ∨ p3) ∨ p5)) ∧ (p4 ∨ p1)) ∧ (True ∧ ((((p2 ∨ p4) ∧ p2) ∨ p5) → (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186682937201090858796463440869 : (((p2 ∨ (p4 ∧ (p1 ∨ (p3 ∧ p5)))) ∧ ((p4 → p5) ∨ True)) → (p2 ∨ (True → (((True ∧ (((p5 ∨ p2) ∧ p2) → p1)) ∨ True) ∨ False)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39725707240127468671791637279 : (((p5 ∨ (((p3 ∧ ((p2 ∨ p3) ∧ (((p4 → p3) ∨ p4) ∨ False))) ∧ p3) → (p2 ∧ ((True ∨ p2) ∧ (p2 → (p5 ∧ p1)))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52505288916036334311560541622 : (((((p3 ∧ ((((p1 ∧ p3) → p3) → False) ∧ (p5 → p4))) → p2) ∧ p1) ∨ (((((p3 ∧ p1) ∧ p3) ∧ False) ∨ True) ∨ (p3 → p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190816667569721477617417554002 : (((p2 ∧ (p5 ∨ ((False ∨ False) ∧ False))) ∨ (p5 → p4)) ∨ (p3 ∨ ((True ∧ (False ∧ (p5 → p1))) → ((p2 ∨ p2) ∧ ((p2 ∧ p5) → False))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66048333542209654108491946935 : ((p5 ∨ ((((p1 ∨ p2) → (p3 ∨ ((p4 → p1) ∨ (p1 → (((p5 → p4) ∧ (False → ((p4 ∧ p1) ∨ p4))) → p1))))) ∧ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784879169140276892476990400821 : (((p3 ∨ (p2 → ((((p4 ∧ ((p2 ∨ (p1 ∨ (False ∧ p5))) ∧ (p4 ∨ (p3 ∨ (p4 → False))))) ∨ (p3 → (p2 ∨ p5))) ∨ p3) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207846588521270347501621147665 : ((((p1 → True) ∧ p3) ∧ (p5 ∨ False)) → (True ∧ ((False ∨ (((p4 ∧ (p1 → p2)) ∧ (True ∨ (p2 → p5))) → (p1 ∧ (p4 ∨ p4)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224587973183428819674165266251 : ((p2 → (False → p5)) ∧ (((p5 → p2) ∧ False) ∨ (p5 → (((p2 ∨ (p2 → (True ∧ (p2 ∧ ((False → p4) → p1))))) ∧ (True → p3)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249498561149845055679430219214 : ((p5 ∨ p1) ∨ ((((p4 → (p2 → p1)) ∧ p1) ∨ p2) ∨ (False → ((p4 → (p2 ∧ ((p4 ∧ True) → (p1 ∧ True)))) → (p1 → (p4 ∨ p3)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40507725359575047588919553282 : ((((p2 ∧ ((p1 ∧ (((False ∧ ((p5 → p1) → False)) ∧ ((p3 ∧ p5) → (True → (p5 → p1)))) ∧ p5)) ∧ (p2 ∨ p5))) ∨ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110954051705257391289849871912 : (((((((p3 ∧ True) → (p5 → (((p3 ∨ False) ∨ p3) → (p3 ∨ p3)))) ∧ ((p4 ∧ p1) → p1)) → p5) ∨ (p1 → p5)) ∧ False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613822927288626757082900654751 : (((((p5 → ((p1 ∧ (p1 ∧ (((p4 ∨ p4) ∧ ((True → p5) ∧ ((p3 ∨ p1) → p4))) ∨ p5))) ∧ p2)) ∧ (p2 → (p1 ∧ p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198202173700350480026312661588 : (((p3 → False) → ((p1 ∨ (p2 ∧ False)) ∨ False)) ∨ ((((((False → (p5 ∧ p1)) ∨ p1) → p4) → (True → (p4 ∨ (True ∧ False)))) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → (p5 ∧ p1)) ∨ p1) → p4) → (True → (p4 ∨ (True ∧ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False → (p5 ∧ p1)) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178290748728390857498467179594 : (((p1 ∨ ((True ∧ ((p5 → (False ∧ p4)) → p2)) → p1)) ∧ (p4 ∨ p3)) ∨ (True ∨ (p5 ∧ ((((p2 ∧ (p3 → p1)) → p5) → p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747477425753816650833877377826 : ((((True → p1) → ((((((((True → True) ∨ (False ∧ ((True → False) ∨ p5))) → (p5 → p5)) ∨ (False ∨ False)) → p5) ∧ True) ∨ p2) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_46077661324378355829231840885 : ((((((p3 ∧ p3) ∨ (p5 → (p3 → (True → (((False ∨ p5) → False) → ((p1 ∧ p1) → p2)))))) → (p3 ∧ p4)) ∨ p1) ∧ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350275050156997470197391456471 : (p4 → ((p4 ∧ (p1 → ((((((p3 ∨ (((p2 → p5) → p4) ∧ p2)) ∨ p3) → p3) ∧ p4) → (p1 ∨ p5)) → (True → (p2 ∧ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177770488346183200871960143790 : (((False ∧ ((False ∧ (p4 ∧ (p4 → (p3 ∨ p4)))) ∨ (p1 ∨ p5))) ∧ p3) ∨ (((((p1 ∨ (p5 ∨ p2)) ∧ (p2 ∧ False)) → p5) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202666113947680944968994158957 : (((False ∧ (p1 ∧ p5)) → (False → p2)) ∧ (((p2 → ((p5 ∧ True) ∨ p1)) ∨ ((p2 → False) ∨ (False ∧ (p4 ∧ (False → (p5 → p1)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67882781478553498613525889055 : ((p2 → ((((p5 ∧ ((((False ∧ p3) ∧ (p2 → p2)) ∨ True) ∧ p3)) ∧ False) ∧ ((p4 → p5) ∨ p4)) ∨ ((p3 → p3) ∧ (p2 → True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914249685063721054373703804552 : (((((p2 ∧ (p5 → ((p4 ∨ (((p4 ∧ p5) ∧ p5) ∨ p2)) ∧ False))) ∧ (True ∧ p5)) ∧ ((((p1 ∧ p4) ∨ p4) ∧ p1) → (p3 ∧ p1))) → p1) ∧ True) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206404126017497792946706604723 : ((p3 ∨ ((p4 ∧ p1) ∨ (p3 ∧ p3))) ∨ (p4 ∨ (True ∨ ((((p5 ∧ p3) ∨ p2) ∧ ((((p2 ∨ True) → p4) ∧ (p4 ∨ p4)) → False)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149559786837049383257864186625 : ((p2 ∧ (((p3 ∨ p1) ∨ p1) ∨ ((False ∨ p4) ∧ ((p4 ∧ ((True ∧ p3) ∧ ((p3 ∨ p1) → p3))) ∨ True)))) ∨ (p1 → (True ∧ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16699819062045465097297866537 : ((((((p1 ∨ p5) ∨ (((((True ∧ (p5 → p1)) → (p4 → True)) → p4) ∨ p1) ∨ p4)) ∨ p3) ∨ (p4 → p5)) ∨ ((p2 ∧ False) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75819804391036485834284920916 : (((((p3 ∧ p4) ∨ ((p4 ∨ (p2 ∨ p4)) ∨ ((False ∨ (p1 ∧ (True → (((False → False) → p1) ∧ (p2 ∧ p3))))) ∨ True))) ∨ p5) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ p4) ∨ ((p4 ∨ (p2 ∨ p4)) ∨ ((False ∨ (p1 ∧ (True → (((False → False) → p1) ∧ (p2 ∧ p3))))) ∨ True))) ∨ p5) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255711533735256119290889721076 : ((p5 ∧ p5) → (p2 ∨ (((((p1 ∧ (p3 ∨ ((p2 → (p4 ∧ p4)) ∨ p2))) ∨ (p5 ∨ ((p3 ∧ p1) → p3))) ∨ False) → p1) ∨ (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82363279929958577727035005338 : (((((p4 ∨ (False → False)) ∨ (True → (p2 ∨ True))) ∧ (((False → (p3 ∧ (p1 ∨ p5))) ∨ True) ∨ False)) ∧ (((p1 ∧ p5) → True) → False)) → p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h10 : ((p1 ∧ p5) → True) := by
            -- Implications on the right can always be decomposed.
            intro h11
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h12 := h3 h10
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h14 : ((p1 ∧ p5) → True) := by
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h16 := h3 h14
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h21 : ((p1 ∧ p5) → True) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h23 := h3 h21
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h25 : ((p1 ∧ p5) → True) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h27 := h3 h25
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h32 : ((p1 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h34 := h3 h32
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h36 : ((p1 ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h37
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h38 := h3 h36
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192256796168841467337129037751 : ((((True → (p1 ∨ False)) ∧ ((p4 ∨ p2) ∨ False)) ∧ p2) → (p4 ∨ ((p2 → p3) ∨ (((p1 ∨ (False → True)) → (p4 ∧ (p2 → True))) ∨ p1)))) := by
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
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37287574916510848614792681511 : ((((p3 ∨ (p3 ∧ (((p2 → p3) ∧ ((p1 ∨ True) ∧ (p3 ∨ p3))) ∨ (((p4 ∧ (p1 ∨ p2)) → False) ∨ (False ∧ p4))))) ∧ p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339797531745383703657244319631 : (p1 → (p5 ∨ ((p2 → ((p1 → ((((p4 → p2) → ((p5 ∨ True) → p4)) ∨ p4) ∧ ((p1 ∨ p1) ∨ (p5 ∧ False)))) ∨ p2)) ∨ (False → p1)))) := by
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
theorem thm_5_vars_245674715080513398715917626669 : ((p3 ∧ p1) ∨ ((p4 ∨ ((p4 ∧ p5) ∧ False)) ∨ (((p1 ∧ (p5 → False)) ∧ True) ∨ ((p4 ∧ ((False ∧ p3) ∧ (True → p5))) → (p1 ∨ False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115190812336275628302107375258 : ((((False → ((p5 ∧ p2) → p2)) → (p2 → (False ∧ True))) ∧ (p3 ∨ (((True ∧ (True → True)) → (p5 ∨ (p3 → p4))) ∨ p3))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51280706975370294754618183786 : (((p1 ∧ (p4 ∨ (((p1 ∧ False) → (p2 → ((((True ∨ p4) → True) ∨ p2) ∨ p1))) ∧ p2))) ∨ (p2 ∨ (((p3 ∨ True) → True) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313370182581027354060455831164 : (p3 ∨ ((p5 → ((p1 ∨ ((((p2 ∨ p2) ∨ (p5 → p3)) ∧ ((True ∨ (True → (p2 ∧ (p4 ∨ p1)))) ∨ (p4 ∧ p1))) → p2)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682908113267347411934720917862 : (((((p1 → True) ∧ (((False ∨ (p1 → (((p5 ∨ False) ∧ p1) ∧ (True → p4)))) ∨ p5) ∨ p1)) ∧ (((p3 → p3) ∧ p1) ∨ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40738031541740544056102396756 : ((((((True → p2) ∨ True) ∧ (((True ∧ ((p1 → False) → ((p1 ∨ True) ∧ ((p5 ∨ p3) → (p2 ∨ p5))))) ∨ p2) → True)) → p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244163749899592273563154393038 : ((True ∧ p4) ∨ ((p1 ∨ p2) → ((p3 ∨ False) ∨ (((((False ∧ (p1 ∨ p5)) → p4) → p1) → (p3 → ((p3 ∨ (p2 ∧ p5)) → p3))) ∨ False)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263149670063580747236619968509 : (True ∧ (((p3 → p1) → ((p3 ∧ True) ∧ ((p4 ∧ ((p2 → ((p1 ∨ False) ∧ ((p3 ∨ p2) ∧ False))) → p2)) → (False ∧ p3)))) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608183627812201414293364059064 : ((((((p3 ∧ (((((((True ∨ p3) ∨ (p1 ∧ False)) ∨ (p3 ∨ p3)) → p5) ∨ p3) → (p3 ∨ False)) → (False ∧ False))) ∧ p5) ∨ True) ∨ p2) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_159897011842488105965465282257 : ((((((p2 ∧ ((p1 ∧ (p2 ∨ p2)) ∧ True)) → (p4 → p2)) ∧ (True ∧ (True ∧ True))) ∨ False) → False) → (False ∧ (p4 ∨ (p5 ∧ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ ((p1 ∧ (p2 ∨ p2)) ∧ True)) → (p4 → p2)) ∧ (True ∧ (True ∧ True))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((((p2 ∧ ((p1 ∧ (p2 ∨ p2)) ∧ True)) → (p4 → p2)) ∧ (True ∧ (True ∧ True))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h25 := h1 h14
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114292715974806242899959648537 : (((((((p5 ∨ p3) → ((p2 → (p5 → (p1 ∧ p4))) ∨ p4)) ∨ p4) → p4) ∨ (True → p3)) ∧ ((True → (p4 → p2)) ∧ True)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124215293982550908054609622048 : (((((((p5 ∧ p4) ∨ p1) ∨ p3) ∨ (True → p1)) ∧ p3) → ((p2 ∧ ((p4 ∨ p3) → p1)) ∧ (((True ∨ p2) ∧ p5) ∧ p3))) → (p3 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p5 ∧ p4) ∨ p1) ∨ p3) ∨ (True → p1)) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



