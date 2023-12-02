variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265905874149976829194475431340 : (True ∧ (True → ((True ∨ (True ∨ (p4 → p5))) → (((((p1 ∨ p2) ∨ False) ∨ ((((p4 → p1) ∨ p2) ∧ p3) ∧ p3)) ∧ (p1 → p2)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
theorem thm_5_vars_666619158259149788922130878872 : (((((((((p2 ∧ p5) ∧ p1) ∧ p5) ∨ False) ∨ ((p4 ∧ p2) ∧ p2)) ∨ ((((p4 ∧ p3) ∨ p5) ∧ p2) ∧ False)) ∧ ((p3 ∧ False) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340091859244589261668385208959 : (p1 → (p3 → ((p4 ∨ ((p1 ∨ (p5 ∧ p3)) ∧ (p5 ∨ (False ∨ (((False ∨ ((p3 ∧ (p4 ∧ p2)) ∨ p4)) ∧ (p2 → p1)) ∧ p4))))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678950445783557912445291901951 : ((((p4 ∧ ((((p5 → p5) → p2) ∧ ((False → p5) ∨ p3)) ∨ (p5 ∨ (p5 ∧ ((p5 ∨ False) ∨ p1))))) ∨ (((p4 ∧ p1) → p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117236732592819460090662109183 : ((True ∧ (p4 ∧ ((p2 ∨ (p1 ∨ ((p4 ∨ (p4 ∧ p5)) ∨ (p3 → (((True → (p1 ∨ p2)) → True) → p5))))) ∨ (False ∨ p4)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351532410998809632784651354623 : (p4 → ((((((False ∨ True) ∧ (p3 ∧ False)) ∧ p2) ∧ p3) ∧ (p3 ∨ ((p3 ∨ p2) ∨ (p2 → p2)))) ∨ ((True ∧ p5) ∨ ((False ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58506795904411874033478950598 : (((p4 ∨ p5) ∧ ((p5 → ((p1 → (True → (p4 → p2))) → (((p5 ∨ p1) → ((p5 ∧ (p2 ∧ True)) ∨ p5)) ∧ (p5 ∧ False)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149650591869194888748592353932 : ((p4 ∧ ((((p4 ∨ p5) ∨ True) ∧ False) ∧ ((True → (((p3 ∧ ((p3 ∧ p3) ∧ p4)) → True) ∨ p5)) ∧ False))) ∨ (p3 ∨ ((False ∧ True) → p5))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310871503016850672123584107392 : (p2 ∨ ((p4 ∧ (False → True)) → (((((p2 ∧ False) → (p3 → (True ∧ p5))) ∧ p1) ∧ ((((False → p2) → (p3 ∧ True)) ∧ p4) ∨ True)) ∨ p4))) := by
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
theorem thm_5_vars_342573237299327190883458504873 : (p2 → ((((p4 → p3) → (True ∧ (p4 ∧ p4))) ∨ (p2 ∧ (True ∨ True))) ∨ ((p1 ∨ (p3 → p2)) ∧ ((p4 → p2) → (p3 ∧ (p1 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59322210880807679666684192797 : (((p4 ∨ p3) ∨ ((((((((p5 → (p5 ∧ True)) → ((p5 → (p1 ∧ p5)) → (p4 → p5))) → p3) ∧ p2) → p4) → p3) ∨ p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260131093572759475995099705506 : ((p2 → p1) → (((p4 ∧ p4) ∨ p5) → (False ∨ (p3 ∨ ((p3 ∧ (((p1 → True) → p3) ∨ p1)) → (p3 ∧ (((p2 ∧ p3) ∧ p2) ∨ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    -- Conjunctions on the left can always be decomposed.
    let h11 := h6.left
    let h12 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    -- Conjunctions on the left can always be decomposed.
    let h21 := h16.left
    let h22 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624264903222524749713881121965 : ((((p3 ∨ ((True → (((p2 ∨ (((p4 → p2) → (p2 ∨ (False ∨ (p3 → ((False ∨ p3) → True))))) → p4)) ∨ p1) ∧ p2)) → p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623078015262356679438897606437 : ((((p5 ∧ (p3 → ((p4 ∨ ((p5 ∨ (p5 → (p3 ∧ (p3 → (p3 → ((((True ∨ True) ∧ p5) ∨ p1) ∨ True)))))) → True)) → p5))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110877854415640576406124349136 : (((((p1 ∨ (True ∧ ((((((p4 ∧ False) ∨ p2) ∨ p4) ∧ p5) ∨ (p3 → p5)) ∧ (p2 ∧ p3)))) → (p5 → True)) → p2) ∧ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314071785758605884030466728391 : (p3 ∨ ((((p5 ∧ p1) ∨ ((False → (True ∧ p2)) ∨ (((p5 → ((p1 ∨ p3) ∨ (p1 ∧ p4))) ∨ p1) ∧ p2))) ∧ (True → p4)) → (p4 ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193587360113707445789949177376 : (((False → True) → (p3 ∨ (False → (True ∨ (p1 ∧ False))))) → (((p4 → p4) ∧ (((p3 ∧ True) → p3) → p4)) ∨ (True ∨ (p2 ∧ (True ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55229439538578448435358210207 : (((((p4 → False) ∨ p5) → (False ∧ p3)) ∨ ((((p1 ∨ (p5 ∧ p1)) ∨ ((False ∧ p3) ∧ ((True → True) → p1))) ∨ False) ∧ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14669212003136583907704908484 : ((((p5 → ((p1 ∨ (p4 → ((p5 ∧ p2) → ((p4 → (((p5 ∧ True) → True) ∨ p1)) → True)))) ∨ (p4 → p1))) → p4) ∨ (False → p4)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602715777605223161854319094687 : ((((False ∨ ((p2 → True) ∧ ((((p3 ∨ True) ∧ p2) → (((p3 ∧ p2) ∨ p5) ∧ False)) ∨ (((False → p5) ∧ p2) → (p2 ∨ True))))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232732092979310511289172365639 : ((p1 ∧ (False → False)) → (True → (((p4 → ((((p4 → (p2 → (p4 → ((p3 ∨ p1) ∨ (p4 → p2))))) → p3) → p3) → False)) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683811674632981163013647616588 : ((((((((False ∨ (False ∧ p4)) ∨ (p5 ∧ p1)) → p3) ∨ (((p1 → p3) → p1) ∨ p3)) ∨ p2) ∨ ((False → p3) ∧ (p4 ∨ (True → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173088871875545977177053318147 : ((p1 ∨ ((p1 ∧ (True ∧ (p2 ∧ (True ∨ False)))) ∨ (((p1 ∧ p1) ∧ p2) ∧ p2))) ∨ (p1 → ((((True ∧ (True ∧ p3)) ∨ p3) ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767247680317694571671582842551 : (((p5 ∧ ((((p1 → p5) → (p1 ∧ ((True ∧ (((p2 ∨ p5) ∨ (True → ((p1 ∧ p3) → (p2 → p4)))) ∨ p3)) ∧ p1))) → p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185923704387404542605168607232 : ((((p2 ∧ (p5 ∧ True)) ∧ (p1 ∧ (p2 → (p4 → True)))) ∧ p3) → (((False ∧ (p4 ∨ p2)) ∨ ((((p2 ∨ p1) ∨ p1) → p4) ∨ True)) ∧ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h15.left
  let h21 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918714264397687224144704362616 : ((((((True ∨ (p5 → (((p2 ∨ p3) → p4) ∧ p5))) ∧ (False ∨ True)) ∨ p2) ∧ ((p2 ∨ (True ∨ ((p2 → True) ∨ (p3 ∧ False)))) → p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h10 : (p2 ∨ (True ∨ ((p2 → True) ∨ (p3 ∧ False)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h10
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h15 : (p2 ∨ (True ∨ ((p2 → True) ∨ (p3 ∧ False)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h15
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (p2 ∨ (True ∨ ((p2 → True) ∨ (p3 ∧ False)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54562545300601439354953218939 : (((p4 ∧ ((p1 ∧ p4) ∨ (p2 ∧ (False ∨ p3)))) ∨ (((((p3 ∨ p5) ∨ ((p5 ∧ False) → True)) ∧ p5) ∧ (p2 ∧ (p3 ∧ False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336131747391143013044076449095 : (p1 → ((((p4 ∨ p4) ∨ ((p5 ∨ (p3 ∨ ((((p3 → (p5 → False)) ∧ p4) ∧ p4) ∧ (p1 ∨ (p3 → (p3 ∨ True)))))) ∧ False)) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348242331090709374746727509622 : (p3 → (True ∧ (((p1 → (True ∧ ((p1 → ((p3 ∨ (True → False)) ∧ (False → False))) → False))) ∧ (True → (p4 → ((p2 ∨ p1) ∨ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330298359741639065364502588506 : (True → (p1 ∨ ((False ∧ (((((p3 ∨ False) ∧ (False → True)) ∨ (True ∨ (True → p5))) → (p1 ∧ False)) ∨ (((p4 ∧ p4) ∨ p4) → p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97271727130424834955458351927 : ((p2 ∨ ((((p2 → (((p5 ∧ ((p3 ∧ p5) ∨ p3)) ∨ (p2 ∨ p4)) → p1)) → (p3 ∨ p2)) ∨ True) → (((True ∨ p1) ∧ False) ∨ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p2 → (((p5 ∧ ((p3 ∧ p5) ∨ p3)) ∨ (p2 ∨ p4)) → p1)) → (p3 ∨ p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80985348783537526378097920339 : ((((((True ∧ p3) → ((True ∧ p4) ∧ ((True → False) ∨ p1))) ∧ ((p5 → p4) ∨ False)) ∧ ((p3 ∧ True) ∨ p4)) ∧ (p1 → (p4 → p2))) → p4) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (True ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171848078612351861293121711527 : ((((p4 ∧ p1) ∨ ((((False ∨ p2) ∨ p4) ∨ (p4 ∧ p5)) → (True → p2))) → False) ∨ ((((p5 ∧ ((True ∨ True) ∧ True)) ∨ p1) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249061375931047787263072137233 : ((p4 ∨ p1) ∨ ((p2 → ((True ∨ True) ∧ (p4 ∧ (((((False → p5) ∧ p1) → False) → (False ∨ (p3 ∨ (p2 ∧ p1)))) ∨ p5)))) → (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164874037851920768700489204291 : (((True → (((p1 → ((p1 ∨ (p1 → p3)) ∧ p1)) → p4) ∨ (False ∧ (p3 ∨ p4)))) ∨ p2) ∨ (((p4 → (p3 ∧ p4)) ∧ p1) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112645713795898578544272543947 : ((((p5 → ((p4 ∨ (((((p1 → p1) ∧ (True ∧ p1)) ∧ True) ∧ p2) ∨ (p4 → p4))) → (p2 ∨ False))) → (p2 ∧ p1)) → p4) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232991880402470064867209572463 : ((p3 ∧ (p4 → p2)) → (((((((p3 ∧ p5) ∨ ((True ∧ p5) → (p5 → p5))) ∧ False) ∨ p2) ∧ (p1 ∧ (p2 ∧ p5))) ∧ p5) ∨ (False → p3))) := by
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
theorem thm_5_vars_314431792392681414720024399638 : (p3 ∨ (((p3 → p5) ∨ (False ∨ (True ∧ (((((True ∨ p2) → True) → (p1 ∨ p4)) ∧ (False ∧ p3)) ∨ True)))) ∨ (((p5 ∧ True) → p2) ∧ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38100710539196075039143527541 : ((((p2 → (p2 ∨ (True → (((((((False ∨ False) ∨ p5) ∧ p3) ∨ p1) → p1) ∨ (p1 ∨ True)) → (p3 ∨ p4))))) → (p3 → p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316538147644462991967295643266 : (p3 ∨ (p2 ∨ (p2 → (((p5 → (p1 → p1)) ∧ p5) ∨ ((p2 → p2) → ((True ∨ (p1 ∨ (p3 ∧ True))) → ((False ∨ (p3 ∧ p1)) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191006051938533546079530637444 : (((p3 ∧ (True → (p1 → p2))) ∨ (p5 ∧ (p2 → False))) ∨ (((False ∧ ((((p3 ∨ p4) ∨ p3) ∧ p5) → True)) ∨ ((p1 → p2) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225180699772106836057721208619 : (((p4 ∧ p1) ∧ p1) ∨ (((((p1 ∧ p3) ∧ (p3 → False)) → (True → p2)) → (p1 ∧ p2)) ∨ (((((True ∧ False) → p3) ∧ True) ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_52501974696351296999956476424 : ((((((p4 → ((p2 ∨ ((p4 ∧ p2) ∧ p1)) ∨ p1)) ∨ False) ∨ p4) ∧ p1) ∨ (p3 ∧ ((True → ((p2 → (p3 ∨ False)) ∧ p1)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55072521938593123100453141923 : (((p5 ∨ ((p1 ∨ (p3 ∧ p2)) ∨ p3)) ∧ ((p5 ∨ p2) ∨ (p4 ∨ (p1 → ((p5 → (p1 → p4)) → (p1 ∧ ((False → p4) → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734352210402567210286069486746 : ((((False ∨ p3) ∧ ((False ∨ p5) ∧ ((((False ∧ ((p4 ∧ (p1 → p1)) ∧ p5)) ∨ False) ∧ (((True ∨ p5) ∨ (p3 ∧ True)) → False)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657198116090470516306167303272 : ((((((True ∧ p5) ∨ p1) → (((p3 → True) → p5) ∨ (p5 ∧ ((p3 ∨ p2) → ((p4 ∨ p5) ∧ (p3 → (p2 → True))))))) ∨ (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112152365674616109788687484197 : (((p2 ∧ (((False ∨ p2) ∧ (p5 ∨ (((p4 ∨ False) ∨ (True ∨ (((p1 ∧ p1) ∧ p4) → p4))) ∧ (p3 ∨ p3)))) ∨ p3)) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46943603134534337044689136075 : ((((p2 ∨ (True → ((((p4 → p2) ∨ p3) ∨ ((p3 ∨ (True ∧ ((p5 ∧ p2) ∨ (p1 ∧ True)))) ∧ True)) ∨ False))) ∨ p2) ∨ (True ∧ True)) ∨ p2) := by
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
theorem thm_5_vars_38857224031296262846638609624 : ((((p1 ∧ (p2 ∨ p4)) ∧ ((((True ∨ (p2 ∨ p3)) ∧ (p1 → p2)) ∧ ((p4 → p4) → (p2 → False))) ∨ (p5 ∧ (p3 → False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48765057750278444813730302377 : ((((False ∨ p1) ∨ ((((((p5 → True) ∧ (p5 ∧ p4)) ∧ p5) ∧ (p1 ∨ ((p4 → p3) ∧ p3))) → p2) ∧ False)) ∧ (True ∨ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197755488542961437639907594816 : (((p3 ∧ (p1 ∨ p5)) ∧ ((p2 ∧ p3) ∧ p1)) ∨ (((p3 → True) → (p5 ∧ p1)) ∨ (True ∧ (((((p3 ∧ False) ∨ False) ∨ False) → True) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231191678985979089227215514722 : (((p3 ∨ True) ∨ p1) → (((((((True ∨ (True → p3)) → True) ∨ (p1 ∨ ((p2 → False) → p4))) ∨ p3) → (p1 ∨ False)) ∧ p3) ∨ (p3 → True))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136332221839584030639940888450 : ((((False ∨ p4) → (False ∨ p5)) ∧ ((((p1 ∨ ((p2 ∧ p3) ∨ p5)) ∧ p3) → (p4 ∧ ((False ∨ False) → False))) → p5)) ∨ (p3 → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193299889500087075011537830050 : ((((p5 → False) → p4) ∨ (p3 ∨ ((p4 ∧ p3) ∨ False))) → (True → (((p3 ∨ (False → False)) → p4) ∨ (False → (((True → False) ∧ p3) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114481514501604311002364428693 : ((((p1 → (p3 ∧ ((p2 ∧ (False ∧ False)) ∧ ((p4 ∨ (p5 ∨ False)) ∨ p1)))) ∨ (p2 → p5)) → (((True ∧ True) ∧ p2) ∧ p5)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37982349909540807739029308233 : ((((((p5 ∧ ((((False ∧ False) → (p1 → p1)) ∧ (p1 ∧ p4)) ∨ p1)) ∨ p4) ∨ (p1 ∨ ((True ∧ p5) ∨ p2))) ∨ (p2 → p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346770769144436762763292141988 : (p3 → (((((p5 → False) ∧ ((((((True → p3) → p5) ∨ True) → False) ∧ (True ∨ p5)) ∨ p3)) ∨ p5) → False) ∨ (((p2 → False) ∧ p2) → p3))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211326681501500811918701179678 : (((p2 ∨ True) ∨ (p4 ∧ p2)) ∧ (((((p2 ∧ ((p2 ∧ p2) ∨ p2)) ∧ p3) ∧ p1) ∨ ((False → True) ∨ (p5 → False))) ∨ (p3 → (p4 ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257684457097126271553754442890 : ((p3 ∨ p3) → (((p5 ∧ (p5 ∧ True)) ∨ (p5 ∨ (((((p4 → ((p5 ∨ (p4 ∧ False)) ∧ p2)) → p1) ∨ p2) → p3) → True))) → (p4 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197763490794253698895189433842 : (((False ∨ (p5 → False)) ∧ (p3 → (p2 → p2))) ∨ (p3 ∨ (p2 → (((p5 ∨ (p5 → True)) ∨ p2) → (True → (p5 → (p3 ∨ (p3 → p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_566002833666471876504241393198 : (((True → ((p4 ∨ (((p2 → p5) → True) ∨ (p1 ∧ (p4 ∨ p1)))) → ((True ∨ p2) → (p4 → ((((p1 ∧ True) ∨ True) → False) ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596785662469730538071489356232 : ((((((((False ∧ True) ∧ p4) ∧ p1) ∧ False) ∨ (p3 ∧ (((p5 ∨ True) ∨ p4) ∧ (p2 ∧ (p1 ∧ ((False ∨ (False ∨ p2)) ∨ True)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230681459210230958538669950558 : (((p4 → True) ∧ p3) → (((p1 → False) ∧ ((((p3 ∨ ((p3 ∧ (p3 → True)) ∧ True)) ∧ (p5 → p2)) ∨ (p2 ∨ False)) ∨ (True ∨ p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244543028772695176183664073250 : ((False ∧ p3) ∨ (p2 → ((p5 ∧ ((((p1 ∨ (p1 ∧ p4)) ∨ p2) ∨ (p1 ∧ p1)) ∧ p1)) ∨ ((True ∧ (p3 ∨ p3)) ∨ (p2 → (False → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137143338300039140326344188633 : ((True ∧ (p1 → (p4 ∨ (True ∧ (p5 ∧ (p3 ∨ ((p5 ∨ (((False → (False ∧ p1)) ∧ (p4 ∧ p2)) ∧ p2)) ∨ p2))))))) ∨ (p4 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322330876736308371868571078123 : (p5 ∨ ((((((p2 ∧ p2) → (((p5 ∨ p3) ∨ p3) → p5)) ∧ p3) → (((p1 ∧ ((p2 → False) ∨ p1)) ∨ p1) ∨ p3)) ∨ (p3 ∧ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164929334836294788212679972303 : ((((((False → p4) → (True → False)) → ((p1 ∧ p3) ∨ (p1 → (True ∧ p4)))) ∨ p2) → p4) ∨ ((False → (True ∧ False)) ∨ (p5 → (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317859069881466005498519027051 : (p4 ∨ (((False ∧ p2) ∨ (((p5 ∧ ((True → p4) → (True ∨ p3))) → (p5 ∨ False)) → ((p2 → (True ∧ ((p3 ∨ p2) ∧ False))) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765106048205078297842754175238 : (((p4 ∧ (((((p1 ∨ (True → ((p4 ∧ p5) → (((p5 → True) → p5) → (True ∧ (False ∧ False)))))) ∨ p5) ∧ p1) ∧ True) ∨ (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341008626379618166217288192845 : (p2 → ((p1 ∧ (((p1 ∨ p1) ∧ ((p1 ∧ (p1 ∧ (p1 ∨ p3))) ∧ (p4 → (p1 → ((p1 ∨ (p2 → p3)) ∧ False))))) ∨ (p2 ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245489062536484267252310836910 : ((p2 ∧ p5) ∨ (((((p2 → p3) ∧ False) ∨ False) ∧ (p4 ∧ p2)) ∨ (True ∨ (((p4 ∨ p4) ∨ ((False ∧ False) → (p5 ∧ False))) ∧ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157360394653991946685797507400 : (((p1 → (((p3 ∨ True) ∨ p5) ∧ (p1 → (p1 ∨ ((p5 ∧ (p4 ∧ (p5 → p4))) ∨ p4))))) → p3) ∨ (p2 → ((p1 ∨ (False ∨ p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206889402786436270105496036823 : ((((p3 → (p2 ∧ p1)) ∧ p5) ∧ p4) → (p4 ∧ ((((True → (True → (p2 ∨ False))) ∨ (True → p2)) ∨ (p4 ∧ p4)) ∨ (p1 ∨ (p2 → True))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125747911062968496584370945948 : (((p4 ∨ p4) ∨ (((p1 ∨ False) ∨ (p4 ∨ (p5 → ((True → (False ∧ ((p1 ∨ False) → (True ∨ (p2 ∨ True))))) ∨ p5)))) ∧ p2)) → (p3 ∨ True)) := by
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
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112015031616545102774827782740 : (((((p1 ∧ False) ∧ p3) ∧ ((p5 ∧ p4) ∧ (((p4 ∧ (((True → p5) ∨ False) → (p1 → False))) → (p3 ∨ p4)) ∧ p3))) ∨ p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20407296069658354365114726092 : ((((False ∨ (p1 ∧ (p3 ∧ ((p3 ∨ p5) → ((p3 → p1) → False))))) → p4) → (False ∨ ((((p5 → p4) ∨ p1) → (p1 → p5)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633931551608644684069678268937 : ((((((((p3 ∧ (True ∨ (False ∨ (p1 → False)))) ∧ ((p3 → p3) ∨ (True → (p1 ∧ False)))) → (p2 ∧ True)) → p3) → (p3 → p2)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134343133857247297691225265625 : (((p5 ∧ ((((p1 ∨ (((p4 → p1) ∧ False) ∧ p4)) → ((False ∨ p3) ∧ p5)) ∧ (p5 ∨ (True ∨ p2))) ∨ p2)) ∨ p5) ∨ (False → (False ∧ p1))) := by
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
theorem thm_5_vars_117796601911925147586415909194 : ((p4 ∧ (((p5 → (p2 → False)) → ((p3 ∧ p4) → p2)) → (p4 → ((p4 → p3) ∨ (False ∧ ((p1 ∧ (p1 ∨ p4)) → p1)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41172696841367256090970673559 : ((((((p3 ∧ (((True → p5) ∧ p5) ∨ ((False ∨ p4) ∧ (p4 ∧ True)))) ∧ ((p2 ∧ p3) ∨ p3)) ∨ p5) → ((True ∨ p4) ∧ p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304684840876395479542140680600 : (p1 ∨ (((((p3 ∧ ((p1 ∧ ((p4 ∧ (p5 ∨ p3)) ∨ ((p3 → p4) ∧ p5))) ∨ (p4 → p3))) ∧ (False ∧ True)) ∨ True) ∨ p1) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262331715425239711506572522227 : (True ∧ ((((False ∧ (p3 ∧ (p4 ∧ True))) ∧ p3) ∨ (p2 ∨ ((True → (False → (((p1 ∧ (p5 ∨ (p2 → p2))) ∨ p4) → p3))) ∨ p2))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h2
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610497447644504906002491549281 : ((((((True → ((p5 ∧ p2) → (p1 ∨ (p2 ∨ (p2 → (True ∧ ((p5 ∨ True) → ((p5 ∧ (False → p4)) → p2)))))))) → p2) → p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64564279547703862161014214435 : ((p1 ∨ (((p4 → p3) → p5) ∧ (((False ∨ p5) ∨ ((True ∧ (p5 → ((p3 ∧ p2) ∨ False))) ∧ p3)) → ((p2 ∨ (False ∧ p1)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798275100893142095992286896196 : (((p1 → (((p3 ∧ (((True → True) → (True ∨ ((p5 ∧ False) ∧ (p4 → p1)))) ∧ True)) → p4) → ((p3 ∧ p5) ∨ ((True → p2) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356877396854034913611281161372 : (p5 → ((p2 → ((p1 ∧ p4) ∧ p5)) ∨ ((((p2 → p2) → ((p4 → p2) ∧ p2)) ∧ p5) ∨ ((True ∧ (((p3 ∧ p1) → True) → True)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116463587928737610322750373602 : (((False ∧ p1) ∧ (((((((((p1 → (p3 → p5)) ∨ p5) ∧ p3) → p3) ∨ False) → (p4 → p1)) ∨ p4) ∧ p1) ∧ (p4 ∨ p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166665007133375962566455811781 : ((p1 → (p5 → ((((p3 ∨ p5) ∧ ((p1 ∨ (p2 → p5)) ∨ (p5 ∧ p3))) ∨ True) ∧ p2))) ∨ (((p4 → p2) ∨ True) → (p5 ∨ (p4 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40626882111713703090603931599 : ((((((((((False ∧ p4) ∨ (False ∨ ((p1 ∨ p3) ∧ (p2 → p4)))) → (p3 ∧ (p3 → False))) → p1) ∨ True) ∨ p4) → p5) → p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158583325159119865027896374429 : ((True ∧ (p4 ∧ (p3 ∨ (p4 ∨ ((p3 → ((p3 ∨ (False ∧ (False ∨ p1))) → p1)) ∨ (p4 ∧ p2)))))) ∨ ((((p5 → p3) → True) ∧ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205239221437723424137597592052 : ((((p2 ∧ p4) ∨ p1) ∨ (p3 ∧ p5)) ∨ (p3 → (((((p2 ∨ p1) ∧ (False → ((p4 → ((p4 ∧ p1) ∨ False)) → p5))) ∨ p5) ∨ p1) → p3))) := by
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
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350777804251936107105908495483 : (p4 → ((p4 → (p1 ∧ (((((p3 → (p4 ∧ False)) ∧ (p3 ∨ (p4 → (False → (p4 ∨ p1))))) ∨ (False ∧ p2)) ∨ (p5 ∨ False)) ∧ False))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60707293709335225787964896102 : ((True ∧ ((False ∨ (p3 ∨ ((p2 ∧ (p3 ∧ p4)) ∨ p1))) ∨ ((p4 ∧ (p5 ∨ p4)) → (((True ∨ p3) → (p1 ∨ p2)) → (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656259610646119940380972289763 : (((((((p3 ∧ p4) → (p3 → (p4 → ((p5 ∨ False) ∧ True)))) → p5) ∧ ((p2 → ((p5 ∧ p5) → p1)) → (p4 → False))) ∨ (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15254262867062594650102931656 : (((p5 → (((((p5 ∧ ((p2 ∨ p4) ∧ ((p5 ∧ (p1 → (p4 ∨ p3))) ∧ False))) ∨ p5) → (p5 ∧ False)) → p1) ∧ True)) ∨ (p3 ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∧ ((p2 ∨ p4) ∧ ((p5 ∧ (p1 → (p4 ∨ p3))) ∧ False))) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117708767348209196419555432193 : ((p3 ∧ (p4 ∧ ((((True ∧ p3) ∨ (False ∧ (p5 ∧ ((p2 → p4) ∨ p1)))) ∧ ((p4 ∧ p5) → (False → (p3 → True)))) ∨ p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347822176273411999671937124629 : (p3 → (((False → p5) ∧ p2) → (((((False ∧ ((False ∨ False) ∧ p3)) → (p1 ∨ (p5 ∨ p4))) ∨ p4) → ((p5 ∧ p3) ∨ p5)) ∨ (False → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84114982004144222357408685324 : ((((p2 → p3) ∧ (((False → (False → p5)) ∨ ((p1 → False) → (True → p4))) → False)) ∧ (p3 → ((p5 ∨ p2) ∨ (p3 → (p2 → p2))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False → (False → p5)) ∨ ((p1 → False) → (True → p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133570244737020816066413077293 : (((((p3 ∨ (((p2 ∧ (p2 ∨ ((p4 → (p5 → p5)) ∧ True))) ∨ p2) → p5)) ∧ ((p1 ∨ p4) ∧ True)) ∨ p4) ∧ p2) ∨ ((p1 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147273219953668143776604451895 : ((((((((p3 ∧ (p5 ∧ (p4 ∨ p3))) ∧ p5) ∨ p2) → p1) → (p3 ∨ ((p3 ∨ p5) → False))) ∨ True) ∨ False) ∨ (False → ((p1 → False) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



