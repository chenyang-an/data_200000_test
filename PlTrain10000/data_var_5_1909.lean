variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612167842336090645621873837204 : ((((((((((p5 ∨ False) → p3) ∨ p1) ∨ (p2 → p2)) → p1) → (p4 ∨ ((p2 ∨ ((True → p2) → p3)) ∧ p5))) ∧ (p2 ∧ p2)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166323913648931947214028646004 : ((p5 ∧ ((p3 ∨ ((False ∨ (p3 ∧ p1)) → (p1 → True))) → ((p3 ∧ (p4 → False)) → p4))) ∨ (((p5 ∨ p1) ∧ ((True → p5) ∧ False)) → p3)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141446703763118720559590356807 : ((((p2 → p3) ∨ p5) ∧ (((p1 → (True → (False ∨ (True ∧ p1)))) ∧ ((p2 ∨ (p5 → (p1 → False))) ∨ p1)) ∧ p2)) → (p1 ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117282432681731257000559964878 : ((False ∧ ((True → ((p4 → (((p5 ∧ ((((False ∨ True) ∨ p3) → p5) → p2)) → (p5 ∨ (p2 ∧ p5))) → p2)) ∨ p3)) ∨ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347657995815042802503572216417 : (p3 → (((p1 ∨ True) ∨ (False → p4)) → ((p5 ∨ p1) ∨ (p3 ∨ ((((((True ∧ (False → (p1 ∧ True))) → p1) ∧ p5) ∨ p4) → p4) ∧ p4))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148160156083084405967775682740 : (((p4 → ((p2 ∨ ((((True ∧ ((p1 ∧ p5) ∧ p3)) ∧ p1) ∧ True) ∨ p5)) ∧ (p3 ∨ False))) → (p1 ∧ p4)) ∨ (p1 → (False → (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350095053450094075764184465963 : (p4 → (((((False ∨ ((p5 ∧ True) ∧ (p3 ∧ p4))) → False) ∧ (p3 ∨ ((p5 → (p3 ∨ p1)) ∧ (p3 ∧ False)))) ∨ ((p2 ∧ True) → p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258785436979782491512076803399 : ((True → False) → ((((True ∧ True) ∧ ((p4 ∧ False) ∨ True)) ∧ (((p5 ∧ p4) ∨ p2) ∨ p1)) → (p5 ∨ ((p4 → (False → p3)) → (False ∧ p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h19 := h1 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256702923442161143275734009970 : ((p1 ∨ p1) → ((p4 → (((((p5 ∨ (p4 ∨ (((p4 ∨ p1) ∨ p5) → p5))) ∧ p2) → p3) ∨ p2) → ((True → False) ∨ (p5 ∨ p5)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40567018595388854173893458286 : ((((p4 → ((p5 ∧ (((p4 → p2) ∨ (False → True)) → ((p3 ∨ p3) ∨ (True → p2)))) → (p1 ∧ (True ∧ (p3 ∧ p4))))) ∨ False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303824745078690406367476808072 : (p1 ∨ (((((((p2 ∧ (p3 → ((False ∧ True) → p5))) → (False ∨ False)) ∧ (False → p1)) → (p3 ∨ (p5 ∨ p1))) → p4) ∧ (True ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701503952652948271674075331334 : (((((False → (p3 ∧ True)) ∨ (True ∧ ((p5 → p2) ∧ p1))) ∧ (p1 ∨ ((p1 ∧ (p4 ∧ p1)) ∨ ((p3 ∧ ((p3 ∨ False) → True)) → p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82418229961593879580378194851 : ((((p5 → False) ∧ ((((p2 → p3) → (False ∨ p5)) → p2) ∧ ((p1 → ((p4 ∨ p2) → False)) ∧ True))) ∧ (False ∨ ((p5 → p4) → p2))) → p2) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p5 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h16 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178428425096793752645183649417 : (((((p1 → (p1 ∧ (p1 ∨ True))) ∧ False) ∧ p4) ∧ (p5 ∨ (p2 ∨ False))) ∨ (((p3 ∨ (((p3 ∨ True) ∧ True) ∧ p3)) → True) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51114104835407021977972651616 : (((((p5 ∧ (((p4 ∨ (((p1 ∧ (p2 ∧ p4)) ∨ True) ∧ p3)) ∧ p1) ∧ p3)) ∨ p3) ∨ p3) ∨ (True ∨ ((p3 ∨ p4) ∧ (p3 ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764820260828830735828057787602 : (((p4 ∧ (((((p3 ∧ p2) ∧ p1) ∨ ((True → p3) ∨ ((True ∧ ((((p2 ∨ p1) ∨ p1) → True) ∨ True)) → (p2 → False)))) → True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807745493657810326782759120868 : (((p4 → (((p2 ∧ p5) ∨ p5) → (p2 ∧ ((((p3 → p1) → ((False ∨ p1) → ((True ∧ p2) ∧ (p1 → p4)))) ∨ True) ∧ (p4 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45850901349745381891477810159 : (((p2 → (p5 ∨ ((((((p3 → (((p4 ∧ p1) ∨ (p4 → p4)) ∧ p5)) ∨ (p4 ∧ (False → False))) ∨ p2) ∧ True) ∧ p4) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147183010772061334563781051736 : (((p2 ∨ (True → ((((True ∧ (p1 → p4)) → p2) ∧ p4) ∨ (((False ∨ False) ∨ p2) ∨ (p5 ∧ p5))))) ∧ p5) ∨ ((True ∧ p4) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308689243008662549470161464719 : (p2 ∨ ((p1 ∨ (p3 ∧ (False ∧ ((((p5 → p1) ∧ (True ∨ p3)) ∨ ((p2 ∧ (p4 ∨ p4)) ∨ (True ∧ p2))) → ((False → p4) ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204970556160927887589192081302 : (((p1 ∧ (p5 → (p4 → p2))) → p3) ∨ (((p2 → p1) ∨ p3) → ((p3 ∧ ((p2 → p2) ∧ ((p2 → p4) ∨ p2))) → ((p2 ∨ True) ∨ True)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
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
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111048993614821747182625514357 : (((((p5 → (p4 ∧ (((False ∨ True) ∨ (((p1 ∧ p5) → p1) → p2)) ∨ True))) ∧ True) → ((False ∧ (p2 → True)) ∧ p1)) ∧ p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231816328611140004030505759763 : (((p4 ∧ p5) → p1) → (True → ((p5 ∨ ((True ∧ (True ∧ ((p2 ∨ False) ∧ p4))) → ((((False ∨ (p5 → p5)) ∧ p2) ∨ p1) ∧ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328317886833739341469542872453 : (True → (((((True ∨ ((p2 ∨ p2) → p5)) ∧ (p3 ∧ p2)) → ((False ∧ (p2 ∧ (True ∧ p4))) → p5)) ∧ True) → ((True → p4) → (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43792088301987473396105429230 : ((((p4 ∨ ((p2 ∨ (((p5 ∨ True) ∧ p1) ∨ (p2 ∧ (True → (((p5 → (p2 ∧ p2)) → False) → p1))))) ∧ (p4 ∨ p4))) → True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198527811306183806377118671343 : ((False ∨ (((False ∨ True) → p5) ∧ (p2 → False))) ∨ (p3 → (p4 ∨ ((((((p1 → False) → p1) ∧ p5) ∨ True) ∧ ((p5 → False) ∨ p3)) ∨ True)))) := by
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
theorem thm_5_vars_87304843691651043663972138514 : (((((p3 ∧ p3) → p1) ∧ (p1 ∧ True)) ∧ ((False → (((p5 ∧ p5) ∨ (p3 ∨ True)) → p5)) ∨ (p2 ∨ ((p1 → p4) → (p1 → p5))))) → p1) := by
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
  cases h3
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738159719981585300918596515298 : ((((False ∧ p2) ∨ (((p2 ∧ (False ∧ p5)) ∧ (((True ∧ p1) ∧ p4) ∨ (((p3 → (p5 ∨ True)) → p1) ∧ p1))) ∨ (True ∨ (p2 ∨ p4)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_22164486968824485414423672518 : ((((p2 ∧ True) ∨ (p1 ∨ ((False ∧ p4) ∧ p1))) ∨ (p1 ∨ (((p5 ∧ (False ∨ ((False → p2) → True))) ∧ False) → (p1 ∨ (p3 → False))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136279239552761931704998469731 : ((((True → (p1 ∧ p2)) → (p5 ∧ True)) → (((False → (p3 ∨ (p5 ∨ True))) → (p4 ∧ p3)) ∨ (False → (False ∨ p1)))) ∨ ((p5 ∧ p5) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183957476072614083487422907905 : (((True → ((p4 → p2) ∧ (True → ((p2 ∨ p5) ∧ False)))) ∧ False) ∨ ((p2 → ((False ∧ (((p5 → False) → p3) → p3)) ∨ (False → p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44002070251620921619771930051 : (((((p1 → (((False → (p4 ∧ ((((p3 ∨ p5) ∨ p1) → (p4 ∨ p3)) ∧ p5))) ∨ p1) → p3)) ∧ (p5 → p4)) → (p3 ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52690184113991254906037901410 : (((True → ((False ∧ p1) ∧ (p4 → ((False → False) → ((p3 ∨ p2) ∨ p4))))) ∨ ((p5 ∨ p4) ∨ (False → (True ∧ ((False ∧ False) → p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172452961154588928350066639967 : ((((p3 ∨ p2) ∨ (p2 ∧ p5)) ∨ (((p3 ∧ p4) → False) ∨ (p3 → (False ∧ False)))) ∨ ((p4 ∨ p4) → (True ∨ (p3 ∨ ((p4 → True) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769764809121258271417863161437 : (((p5 ∧ (p3 ∨ (((((((p1 ∨ (True ∧ p2)) → (p1 ∧ p4)) ∧ ((p3 → False) ∧ p1)) ∨ False) ∧ (True ∨ True)) ∧ (True ∨ p4)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113617583419617663074429100853 : (((True → ((p3 ∨ (((True ∧ (((False ∧ (p4 → (p1 → (p5 ∨ p2)))) → p2) ∧ False)) → p4) ∧ p1)) → p4)) ∨ (False ∧ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344813148944020560121780304050 : (p2 → (p4 → (p4 ∧ ((((False → ((False ∧ (p1 → p1)) ∧ p4)) → ((p4 → p3) ∧ (True ∧ (False ∨ p3)))) ∧ (p1 ∨ p1)) ∨ (True ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40314861135229425752479472898 : ((((((p2 → p4) ∨ (p5 ∧ ((p5 ∧ ((p4 → (p5 ∧ True)) ∨ (((True ∧ p3) ∧ True) → (p3 → True)))) → p3))) ∧ False) ∨ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671247114834370012982476419147 : ((((p4 ∨ ((False ∧ ((p4 → p1) ∧ p4)) ∨ (p2 ∧ (((p4 ∧ p4) ∧ (p1 ∧ p3)) → ((p1 ∧ p2) ∧ False))))) ∨ ((True → True) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855800465477257551850081259329 : ((((((((p1 ∨ ((p2 → (p3 ∧ False)) → ((p3 → p4) → ((((p5 ∨ p5) ∧ p2) ∧ p3) ∨ p3)))) ∨ p2) → p3) → p4) ∨ True) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∨ ((p2 → (p3 ∧ False)) → ((p3 → p4) → ((((p5 ∨ p5) ∧ p2) ∧ p3) ∨ p3)))) ∨ p2) → p3) → p4) ∨ True) := by
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
theorem thm_5_vars_233477718711537704363041819632 : ((p1 ∨ (True ∧ p5)) → ((((p1 → p5) → (((p1 → (p3 → p5)) ∧ True) → ((((True → p3) → (p1 → p1)) ∧ p3) ∨ p5))) ∨ False) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114643849990716215213662511118 : ((((((p5 ∨ (((p5 ∧ p1) ∧ p4) ∨ p3)) ∨ p2) → (p3 → False)) ∨ (p5 → p2)) ∨ (p5 ∨ ((False ∨ (True ∧ p4)) ∧ p1))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147963355990143414120396071256 : (((p3 ∨ ((False ∧ p1) ∧ ((p2 ∨ p4) → (False ∧ ((p5 ∧ p2) → ((p4 ∧ False) ∧ p4)))))) ∧ (True ∧ p5)) ∨ (False → ((p1 ∧ p5) ∧ p5))) := by
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
theorem thm_5_vars_39591219675130711885855212900 : (((p2 ∨ (((p3 → False) ∨ ((p3 → (p1 ∨ (p2 ∧ (True ∨ p3)))) ∧ ((((True ∧ p5) ∨ p3) → (p5 ∧ p2)) → p3))) ∧ p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146905068716020725446258641341 : ((((((p5 → ((p3 ∧ (True ∨ (p2 ∧ (p4 → p1)))) → False)) ∧ (p3 ∧ (p5 → p5))) ∨ p4) ∧ False) ∧ p3) ∨ ((p4 ∨ (True ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769976238094905191924508633048 : (((p5 ∧ (p1 → ((((p2 ∧ p3) ∧ (p5 ∨ p5)) ∨ ((p2 → True) ∧ False)) ∧ ((p3 ∨ True) ∧ (p3 ∧ ((p3 ∧ False) ∨ (False ∧ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307253209621896888865074433275 : (p1 ∨ (p2 ∨ (((((p4 → p4) ∧ (p2 → False)) ∨ ((p5 → ((p1 ∧ p5) ∨ p3)) ∨ p5)) → (True → (p2 → (p1 ∧ p3)))) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226356499847251837599072473601 : (((True → False) ∨ p2) ∨ ((p2 → (p1 ∧ ((((False → p5) ∨ True) ∨ (p4 ∨ p1)) ∧ ((((False ∨ p2) ∧ p3) → (p4 ∧ False)) ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789287746043598456802560889056 : (((p5 ∨ ((True → (((p5 → (p2 ∨ p1)) → True) ∨ ((p1 ∧ p4) ∨ ((p4 ∧ p4) ∨ (False ∨ p3))))) → (p2 → ((p2 → p5) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200646227283481359316777279976 : ((p1 ∧ (((False → p5) ∧ (False → True)) ∧ p1)) → ((p5 → (p4 → ((False ∨ p3) ∧ True))) ∨ (p1 ∨ ((p1 ∧ ((False ∧ p2) ∧ False)) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263116740910859913619316831069 : (True ∧ ((((p3 ∨ ((p1 → True) → ((p2 ∧ (False ∨ (p3 → p5))) ∧ True))) ∧ p2) ∧ (False ∧ (((True → False) ∨ True) ∧ True))) ∨ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310323843097235639044173991316 : (p2 ∨ (((p5 → ((p4 ∧ (p3 → (True ∧ True))) → p1)) ∨ p3) → (((p4 → (((False → p4) ∧ True) ∧ (p3 ∧ (p2 ∧ False)))) ∨ True) ∨ True))) := by
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
theorem thm_5_vars_218353404703229351773786954898 : (((p2 → p3) ∨ (p2 ∧ p2)) → ((True → ((((p1 ∧ (p5 ∧ (p4 → (False → (True ∨ (p3 ∨ p2)))))) ∨ p4) ∧ (p3 → False)) ∧ False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345550981222158262395490691157 : (p3 → (((((False → False) ∨ (True ∧ p1)) → False) → (p5 ∨ (p3 → (p3 ∧ (((p5 ∧ p1) → ((False ∨ p4) ∧ (p2 ∨ p4))) ∨ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192715171907530531738864645210 : (((((True ∨ p1) → p4) ∨ ((p1 ∨ p2) ∨ p4)) → p2) → (((True ∧ ((False ∧ False) ∨ p1)) ∧ ((True ∨ False) ∧ (False ∨ p3))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37732740049857900657140869226 : ((((((p2 ∧ (True ∨ p3)) → (p2 ∧ ((p2 → p3) ∧ p1))) ∧ ((p2 ∨ ((p2 ∨ (p2 ∧ p4)) ∨ p4)) ∨ (p2 ∧ p3))) → p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105495621922434662744639112531 : (((True ∧ (((p4 → p1) → (((False ∧ False) ∧ p5) → p5)) → ((p2 → (False ∨ p3)) ∨ p3))) ∨ ((True → (p5 ∨ True)) → True)) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119111275328745235596250885958 : ((p1 → ((p4 → p3) ∧ (((p3 ∨ p4) → (p1 ∨ p1)) → ((p1 → (True → (p5 ∧ ((p4 ∧ p2) ∧ (True ∧ p3))))) → False)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354626759079481971226685207205 : (p5 → (((p1 ∧ ((p5 → (p4 ∧ p5)) ∨ (((((p3 ∧ p1) ∨ (False ∨ True)) ∧ p4) ∧ ((True → p2) → (p1 ∨ False))) ∨ p5))) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164565145228986336976008262791 : ((((p3 → (False ∨ (p2 ∧ p5))) ∨ ((p1 ∨ (True ∨ p3)) → (False ∨ (False → p1)))) ∧ False) ∨ (((False → True) ∨ False) ∨ (p3 ∧ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134300186197854367087316887405 : ((((p4 ∨ p5) → (p2 → ((((p1 ∧ p3) ∧ ((p3 ∧ (True ∨ (p1 → (p1 → p4)))) ∧ p5)) ∧ p1) ∨ p2))) ∨ p5) ∨ (p2 ∨ (True → p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742536668313861128225388199749 : ((((p2 → p1) ∨ ((False ∧ (p3 → (p2 ∨ p2))) ∨ ((((((p1 ∧ True) ∨ False) ∧ (p1 ∧ ((p5 ∧ False) ∧ True))) → True) ∧ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255910248785119351869439149051 : ((True ∨ p2) → ((((p5 → p5) → (((p4 ∨ p2) ∨ (((True ∨ p2) → True) ∧ (p5 ∨ False))) ∨ p3)) ∧ ((True ∨ p2) → (p1 ∨ p1))) ∨ True)) := by
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
theorem thm_5_vars_610872122927103334847729000234 : (((((((True ∨ (False ∨ (True → (((False ∨ p4) → p1) ∧ p5)))) → p4) ∧ (((p1 → False) ∨ (p2 ∧ p4)) ∧ (p3 ∨ p5))) → p1) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_111902093894476873850064538560 : (((((((False → True) → p4) ∧ (p2 ∧ p3)) ∨ (p3 → ((p1 ∧ p1) ∨ p4))) → (p4 → (p4 → ((p1 ∨ p1) ∨ False)))) ∨ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234639645153975097211658965041 : ((p3 → (p3 → p2)) → (((((p3 ∧ p1) ∧ p5) ∧ False) ∧ p2) ∨ (((False ∧ (p5 ∨ False)) ∧ ((False ∧ p1) → (p5 ∧ (p1 ∧ p3)))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245297965204343999077089359796 : ((p2 ∧ p2) ∨ ((p4 → (((((True → p3) ∧ False) ∧ (p5 ∧ p3)) ∨ (p2 → (True ∨ (p1 ∧ (True ∨ p2))))) → p5)) ∨ ((True ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_165885964976744703084163875049 : ((((p4 → p2) ∨ p1) → (p1 ∨ ((((True ∧ (False → (p5 ∧ p1))) ∧ p5) ∧ p2) ∧ p5))) ∨ ((((p1 ∧ p4) → True) ∧ (p2 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667328655934183615954511749148 : (((((p2 ∨ p3) ∨ ((((((p2 ∨ p5) → p1) ∨ p3) ∨ p5) ∧ True) → ((p4 → (p2 → (p3 ∨ p2))) ∧ p2))) ∧ (p4 ∧ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207562260428949370148096780847 : (((((p2 ∧ p4) → True) ∨ True) → p2) → ((((((p1 ∨ True) ∧ (p2 ∧ False)) ∧ (p4 ∧ p3)) ∨ (True → p3)) ∨ p4) ∨ ((False → p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172859652000330347549169140628 : ((False ∧ (p1 ∨ (p1 ∧ ((((p2 ∧ (True ∨ p4)) ∨ (p3 ∨ p5)) ∨ p3) ∧ p5)))) ∨ ((p4 ∨ (p2 ∨ (False → (p3 ∨ p3)))) ∨ (p3 ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185245178523236426298412579206 : ((False ∧ (p5 → (((True ∨ p2) → ((p3 ∨ p3) ∨ p1)) ∨ p4))) ∨ ((True ∧ (p1 ∧ ((p5 ∧ True) ∧ (p1 ∨ (p3 → (p4 ∧ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301263916325685284144246529720 : (False ∨ ((p4 ∧ (p4 ∨ (p1 ∨ (p1 ∨ True)))) ∨ ((p4 ∨ False) → (((p4 ∧ (p4 → ((p3 ∧ True) ∨ ((p1 → True) → True)))) → p1) ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135576619149413411063525027335 : ((((((p2 → p1) ∧ ((p4 ∨ (p1 ∧ (p3 → p1))) ∨ False)) ∨ (p4 ∧ p4)) ∨ p1) ∨ ((p4 ∧ p4) ∧ (p5 ∨ p5))) ∨ (True ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185348778548751615524290406476 : ((p4 ∧ ((p1 ∧ ((p5 ∧ False) ∨ p5)) ∧ (True ∨ (p2 → p2)))) ∨ (p1 → (p1 ∨ (p4 → ((True → p3) ∧ ((p5 ∧ p3) ∧ (p4 ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213480713592479116683055603864 : (((p1 → (p2 ∨ True)) ∧ p2) ∨ ((False → (p2 ∧ False)) → (((p2 → (p1 ∧ (p5 ∨ ((p2 ∧ p3) ∧ p4)))) ∨ True) ∨ ((True → p2) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167631144415084578713094660103 : (((((((p2 → p5) → (False ∧ True)) ∨ (p5 ∨ True)) → p3) ∧ (p4 ∨ p5)) → (p4 → p1)) → (((p4 → ((p2 → True) → p4)) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → ((p2 → True) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641333296589430469366250683362 : (((((p1 → p2) ∨ ((p1 ∧ (p5 ∨ (((p3 ∨ p2) ∨ ((p1 → (True ∨ False)) → p5)) ∨ ((p1 ∧ p2) → p2)))) → (p2 → p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347107821152134444686584584994 : (p3 → ((((p4 → (p3 ∨ (p4 ∨ p1))) → p5) ∧ ((False ∨ (p2 ∧ p4)) ∨ p4)) ∨ (((p3 ∧ p1) ∨ ((p3 ∨ (False → p1)) ∨ p1)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42025298966965993737818399493 : ((((p1 ∧ p1) ∨ ((False ∨ True) → ((p4 ∧ ((p2 ∧ p5) → (p5 → True))) ∧ (((p5 ∧ p4) ∧ False) ∧ ((p2 → p5) ∨ p1))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247289908895091983648337667071 : ((False ∨ False) ∨ ((p5 → ((p1 → (p4 ∧ (p4 ∨ p4))) → ((((p2 ∨ (p5 ∨ p1)) → p1) ∨ (p5 → (True → p3))) ∨ (False ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255909159582471998344902097254 : ((True ∨ p2) → (((((((True ∧ (p4 ∧ (p4 ∨ (p1 ∧ p2)))) ∧ (True ∧ ((p4 ∧ p5) → p2))) ∨ p1) ∨ True) → (False ∧ p5)) → p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((True ∧ (p4 ∧ (p4 ∨ (p1 ∧ p2)))) ∧ (True ∧ ((p4 ∧ p5) → p2))) ∨ p1) ∨ True) := by
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
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((((True ∧ (p4 ∧ (p4 ∨ (p1 ∧ p2)))) ∧ (True ∧ ((p4 ∧ p5) → p2))) ∨ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156863157369884314547735867328 : (((((p4 ∨ ((p2 ∨ p2) ∧ ((p3 → (p4 → p2)) → p3))) ∧ ((False ∧ p4) → False)) ∧ p5) ∨ True) ∨ (((p1 → p1) → p3) → (p3 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249558045369265688310580928358 : ((p5 ∨ p2) ∨ (((p3 → (p4 → p4)) → ((p3 → p2) → p2)) ∨ ((False → (((False → ((p3 ∨ p1) → True)) ∧ (p3 ∧ p1)) → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716801700474993213371613133532 : ((((False ∧ ((p2 ∧ p1) ∨ p1)) ∧ ((((p3 ∨ (p5 ∧ ((p4 → p5) → (p1 ∨ ((p1 ∨ p2) ∧ (True ∨ True)))))) ∧ p4) ∨ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471619518360739247477900889989 : (((((((p3 ∨ (p1 ∨ (p4 ∨ p2))) ∨ (p3 → p5)) ∨ p1) → p3) ∨ (p1 → (((p2 ∨ p5) → (((False ∨ p5) → p5) ∧ True)) ∧ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118467074090449509810644297451 : ((p3 ∨ ((((p3 ∨ False) ∨ (((((p5 ∨ p4) ∨ p1) ∨ p4) ∧ ((False ∨ p1) ∧ p5)) ∨ ((p4 → p4) → p5))) → True) → p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2363505872629927167673671189 : (((True ∧ (((True ∨ (False → p2)) ∨ p4) → (True ∧ False))) ∨ p1) ∨ (p1 ∨ (((p4 ∨ p4) → False) → (p3 ∨ ((p3 → p1) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208147628223081837859323872969 : ((((p4 ∨ True) → p1) → (p4 ∧ p5)) → (((False → p5) → (p4 ∧ (((False ∨ (True ∧ p2)) → (((True → p1) ∧ False) ∨ p4)) ∨ p3))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83156978533664788891226882959 : (((True → (p5 ∨ ((p3 ∧ (False ∧ (True → p2))) ∨ (False → (((p3 ∨ True) ∨ (True ∧ p3)) ∨ p5))))) → ((p5 ∧ False) ∧ (p1 ∨ p1))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p5 ∨ ((p3 ∧ (False ∧ (True → p2))) ∨ (False → (((p3 ∨ True) ∨ (True ∧ p3)) ∨ p5))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157088481399483482287850561031 : (((p5 ∨ (True ∧ (p5 ∨ (p3 ∧ ((True ∧ ((p3 ∨ p2) ∨ p1)) → (False ∧ (p2 → False))))))) ∨ True) ∨ ((p5 ∧ (False ∧ p3)) ∧ (p5 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382385506325956148426523015155 : (((((((False ∧ True) ∧ (False ∨ ((p1 ∨ ((p3 → p2) ∧ (p1 → p1))) → False))) ∨ ((False ∧ ((p3 → p2) ∨ p5)) ∨ False)) ∨ True) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53174871086138774626768860478 : (((((False ∧ (p4 ∧ (True → (p3 ∧ p1)))) → (p3 ∧ p5)) → False) ∨ ((False → p2) → (True ∧ (False ∨ ((p1 → p3) → (True ∨ True)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48320483722601666653717059917 : (((False ∨ (p4 → ((((p1 ∨ p1) → (p5 ∨ (True → (False ∧ (p1 → (p1 ∨ p1)))))) → p4) ∧ (False → (p3 ∨ p1))))) → (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789300284099793865353798867198 : (((p5 ∨ (((((True ∨ (p4 ∧ ((p4 ∧ True) ∨ p2))) → True) → p1) ∧ (p5 ∨ (p1 ∨ p3))) ∧ (((p2 → p4) ∨ p1) → (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119603063093625224511133339327 : ((p5 → (False ∨ ((p1 ∨ ((False ∨ (((p3 ∨ (p4 ∨ ((False ∧ p2) ∧ p2))) → (p2 → p4)) → (True ∧ p2))) ∧ p1)) → p4))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731163171228968214367880805661 : ((((p2 ∨ (p4 ∨ p4)) → ((p5 ∨ ((p2 → False) → ((False → p5) → p1))) ∧ ((p3 ∧ (False ∧ False)) ∧ (False → (p2 ∨ (p5 ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139851137192144769034837412609 : (((p4 → (p2 ∨ ((p4 → p5) ∨ (((p5 ∨ (((p4 ∨ ((p4 ∨ p1) ∨ True)) ∨ p1) → True)) → p4) ∨ p3)))) → p4) → ((p5 → p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (p2 ∨ ((p4 → p5) ∨ (((p5 ∨ (((p4 ∨ ((p4 ∨ p1) ∨ True)) ∨ p1) → True)) → p4) ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611176032349042497889164543203 : ((((((False → (False → p3)) ∨ (((((p1 ∧ (p4 ∧ ((p5 ∧ p5) ∨ False))) ∧ False) → p1) → p5) ∧ ((p1 ∧ False) ∨ p3))) → p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172377239083464082743042644768 : (((p4 → (p3 ∨ (p3 ∧ (p2 → p4)))) ∨ (((False ∨ True) → (p4 ∨ p3)) → p4)) ∨ (((((p1 → p1) ∧ p4) → p1) → (True → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



