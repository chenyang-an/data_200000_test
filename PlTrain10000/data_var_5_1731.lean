variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596201508669235926825687036515 : (((((((True ∨ (p5 ∨ p2)) → p3) ∨ (p1 ∨ p3)) ∧ ((True ∨ (p4 ∨ ((p5 ∧ ((p1 → p1) ∧ p5)) → (False ∨ False)))) → p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717272496481707546473661930278 : ((((p3 ∨ (p5 → (p3 ∨ p5))) ∧ ((((((True ∧ p1) ∧ p3) ∧ p4) ∨ (p2 → (False ∨ False))) → (p3 → ((p1 → p4) → p1))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113316680544223097116270751930 : (((((p2 ∨ p2) ∨ p1) ∨ (p2 ∨ ((p3 → ((p1 ∧ (p5 → (((True → p1) ∨ p4) → True))) → False)) → p5))) ∧ (p5 ∧ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134949714143480692717109381201 : ((((((p5 → p1) → ((False ∨ (p3 ∧ (p2 ∧ True))) ∨ p4)) ∨ (p3 ∨ p4)) ∨ ((p4 ∨ p2) → p2)) ∧ (p3 ∧ p2)) ∨ (True ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214161873893486566909535186447 : ((((p2 ∧ p4) → p5) → p3) ∨ (p2 ∨ (False ∨ ((p4 ∨ (True → ((p5 ∨ p1) → True))) → (False ∨ ((p2 → p4) → (p1 ∨ (p3 → p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217674832898490519175327587846 : ((((False → True) → p2) → p4) → (True ∧ ((((((False ∧ (p4 ∨ p5)) → (((p5 ∨ p4) ∧ (p1 ∧ p4)) → p4)) → p4) ∨ p1) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55845469039295015141723341841 : (((p2 ∧ ((p2 ∧ p3) ∧ p4)) ∧ ((((p4 ∨ ((p3 ∨ (p2 → p4)) ∨ p2)) ∧ (True → (p2 → p4))) ∧ p5) → ((p1 ∨ p3) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52689760412888736610979855987 : (((True → ((((p2 ∨ True) ∧ (p3 ∧ p2)) → True) → (p4 ∧ (p1 ∧ p4)))) ∨ (p2 ∨ ((True ∨ (p1 ∨ (p1 → True))) ∨ (p2 ∧ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41488977765235358281517452884 : ((((((p4 ∨ (p2 ∧ (True ∨ ((p4 ∧ p1) ∧ p3)))) ∨ p2) ∧ True) → ((((p1 ∨ p3) ∧ (p4 ∧ p1)) ∨ (p3 → p3)) ∨ False)) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743415661622713978722116839105 : ((((p5 → p2) ∨ (True → ((False ∨ (p3 → (((p1 ∧ (p2 → p1)) → ((p4 → (p4 → p2)) ∧ p5)) → p1))) ∨ ((True ∨ True) ∨ p2)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39421467503442663050517213430 : (((p4 ∧ (p1 ∧ ((p4 → ((((False → ((p2 → p1) → True)) ∨ ((p2 ∧ p1) ∨ p2)) ∧ p4) ∧ (True ∧ p4))) → (p4 ∧ False)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301364454511616723716877035614 : (False ∨ ((((p3 ∨ p3) ∧ p3) ∨ False) ∨ (((((p1 → ((p3 → p3) ∧ p3)) ∧ (((p3 ∨ p2) ∨ p4) ∧ p5)) ∧ (p1 ∧ p4)) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_191280300457886547741894212425 : (((p3 ∨ p2) ∧ ((((p4 ∨ p3) ∧ p1) ∧ False) ∧ True)) ∨ (True ∧ (p1 ∨ (((p1 ∨ ((p5 → True) ∨ (p1 → p4))) ∨ (True → False)) ∨ True)))) := by
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
theorem thm_5_vars_152143038434138161580400453657 : (((((p3 ∨ (p3 → (p3 ∨ p4))) ∧ True) ∨ p5) ∨ (((((p3 ∨ (p3 ∧ p1)) ∧ True) ∨ p1) ∨ p4) ∨ False)) → (p5 ∨ (True ∨ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325853990082739284100270883176 : (p5 ∨ (p4 ∨ ((((((p5 ∨ p1) → (False ∧ (((p1 ∧ p5) → p2) → ((p1 → p4) ∨ True)))) → ((p4 ∧ p2) → p5)) → p1) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147568051653027114046701887793 : (((((True ∧ (((p5 ∧ p5) ∧ True) → (p4 ∨ ((True → p2) ∨ p2)))) → (p1 ∨ (False → p2))) ∧ p5) → p4) ∨ ((True ∨ False) ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655748606900124183440533884492 : (((((((p3 ∨ ((p4 ∨ p3) → p5)) ∨ (((((p3 ∨ p2) → p5) ∧ False) ∨ p3) → p1)) → False) ∨ ((True → True) ∨ p3)) ∨ (p5 ∧ p3)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308503887406418194635549760172 : (p2 ∨ ((((((p2 ∧ p4) → p2) ∨ p1) ∧ (p5 ∧ (p4 ∨ ((p2 → (p5 → (p5 ∧ p3))) → p4)))) ∨ (True → ((p5 → p5) ∨ p4))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58347760494141688991823773077 : (((False ∨ p4) ∧ (p5 ∧ (p3 ∧ (((p5 → p2) ∨ False) ∧ (True ∨ ((((False ∧ False) ∧ ((False → (p4 ∧ p2)) → p4)) → p5) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322346656467522908149736478650 : (p5 ∨ (((False → ((p3 → (True → (((p3 ∧ True) ∨ (p1 ∧ (p2 ∧ (p3 ∨ (True ∧ False))))) ∨ p4))) ∧ (p5 ∧ True))) → (p5 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681006142823329437606951629863 : (((((True ∧ True) → (((p1 → False) → False) ∧ ((True ∨ (p4 → (p3 ∧ ((p4 ∧ p2) ∨ p4)))) → p2))) → ((True → (p3 → False)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_193361436637629402018165534091 : (((p4 ∧ (p3 ∨ False)) → (p5 → ((p3 ∧ True) → False))) → (((True ∧ ((p4 ∧ False) ∧ p4)) ∧ True) ∨ ((((p1 ∧ p1) → p5) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136769364918368084380483491878 : (((p4 ∨ p5) ∧ (p3 → (((p2 ∨ (p2 → (p3 → ((True → (p5 → p4)) → p2)))) ∧ ((p2 ∧ True) ∧ p2)) → p4))) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181007400897342995480706536489 : (((p1 ∨ False) ∨ ((((p2 → p2) ∧ False) → p2) → (p5 ∧ (p1 ∨ p2)))) → ((p2 ∧ True) ∨ (((((p2 ∧ p3) ∨ True) → p5) → p5) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218920907325200473516125538814 : ((p3 ∧ (True ∧ (p4 ∨ p3))) → (p5 ∨ (p1 ∨ ((p5 ∧ ((p1 ∧ (p3 → (p3 → (p4 ∧ (p1 ∧ (p2 → True)))))) ∧ p1)) → (p5 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- We need to get the left conjuct of h27 based on <expert-advice>.
    let h28 := h27.left
    -- One of the premise coincides with the conclusion.
    exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133836323148554914560210884146 : ((((p3 ∨ p1) → ((((True ∨ (True ∨ p3)) ∧ p1) → p3) → (((((p1 → p1) ∨ p5) → p4) ∧ p5) → False))) ∧ p2) ∨ ((p4 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258081968658244488106260766617 : ((p4 ∨ p2) → (p4 ∨ (p2 ∧ (p4 → (p1 ∨ ((((((((True ∧ (p4 → p2)) ∧ (p3 → p5)) ∨ p3) → p4) ∨ p3) → False) ∨ p2) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908867348016054723280105028551 : ((((((False → p5) ∧ ((((p3 ∨ (p4 ∨ p4)) → False) → p4) ∧ (False ∨ True))) ∨ (p5 ∨ p5)) ∧ (p3 ∧ (p5 ∧ ((p3 → p5) → True)))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h3.left
      let h23 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673444392917674330766837099216 : (((((p2 ∨ ((p5 → False) ∧ p5)) ∧ (((p1 → False) ∨ p3) ∧ ((p4 ∧ (p4 ∨ (False ∨ p5))) → (p5 → True)))) → ((p1 → p3) ∧ p2)) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h27 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h22.left
    let h32 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h34 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h35 := h29 h34
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h37 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h38 := h29 h37
      -- False on the left can always be used.
      apply False.elim h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67291024401084496016412487492 : ((p1 → ((((p1 ∨ (p1 ∨ ((False ∧ p2) ∧ p5))) ∧ (((p4 → p1) ∧ p5) ∨ (p5 → ((True ∧ p2) → (False ∧ p5))))) → False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134573538607648515102901099175 : (((((p4 ∨ ((True ∨ p2) → p3)) ∨ ((((p5 ∨ True) ∨ ((False ∨ p2) → False)) ∨ p4) ∧ True)) ∧ (True ∧ p4)) → p5) ∨ ((True ∨ p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259068779713781766814501500076 : ((True → p5) → ((((False ∧ p1) ∨ ((p3 ∧ (p5 ∨ p5)) ∧ p1)) ∧ ((((p4 ∨ p4) → (((True ∧ p4) ∨ p2) ∧ p2)) → p3) ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634645659885686783965399196988 : (((((p3 → (((p2 ∨ p3) ∧ (((((p2 → (p5 ∧ p4)) ∨ p5) ∧ (p2 ∨ False)) → False) ∨ p2)) → p4)) ∧ ((p3 ∧ True) ∨ False)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39074440324353914044523569163 : ((((p1 ∨ False) ∨ (((((p3 ∨ p5) ∧ True) ∨ ((False → (False ∧ p2)) → p5)) ∧ ((p3 → p1) → (p4 ∧ (p3 → p3)))) ∨ True)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69019160699229547686435477138 : ((p5 → ((p1 → (((True ∨ (p5 ∨ False)) ∧ (p2 → p1)) ∧ (((((p3 → p5) ∨ (False ∨ p5)) ∨ (p1 ∧ p4)) ∨ p1) → p4))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343377088047320761709288709881 : (p2 → ((True ∧ p1) ∨ ((True ∧ (p3 ∨ p4)) ∨ ((p1 → (((p3 ∧ (p5 → (p1 ∧ p4))) ∧ (p3 → (p1 ∧ (p1 ∨ p3)))) ∧ p5)) ∨ p2)))) := by
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
theorem thm_5_vars_313038128116034516572004271175 : (p3 ∨ (((((p5 ∨ (p5 → ((p5 ∨ ((p1 ∧ p3) → p3)) → p2))) ∨ (p3 ∧ ((p5 ∧ (p2 ∧ (True → p4))) ∧ True))) → p4) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59292874144118656723640058094 : (((p3 ∨ p4) ∨ (p4 ∨ ((((True ∨ ((p2 ∧ p1) → p3)) ∧ p2) ∨ False) ∨ ((False ∨ True) ∨ ((True ∧ ((p2 ∨ p2) ∨ p3)) ∨ True))))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47394175281626796095586303197 : ((((p5 → False) → (p4 ∨ ((((p4 ∧ (((p4 → p1) ∧ True) ∨ p1)) ∨ (p3 → True)) ∧ (p4 ∧ (p5 → p3))) ∨ p4))) ∨ (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193513259361703667502113030143 : (((False → p3) ∨ ((((p2 → p4) ∨ p4) ∨ p3) ∧ p3)) → ((((True ∧ True) ∨ (((p2 ∨ p3) ∨ p1) → (p2 ∧ p4))) ∧ p2) → (p4 → p4))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159352819738727831145425785781 : (((((p5 ∨ ((False ∧ p5) ∨ p4)) → (p1 ∧ (p3 ∨ (p2 ∧ (True ∨ (p1 → False)))))) ∧ p2) ∧ p4) → ((p5 ∨ ((True → p5) ∨ p2)) → p1)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p5 ∨ ((False ∧ p5) ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : (p5 ∨ ((False ∧ p5) ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h25 : (p5 ∨ ((False ∧ p5) ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h26 := h23 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342004279629641465384381700846 : (p2 → (((True → p5) ∨ ((p4 ∨ (((p1 ∨ False) ∨ (((((p3 → p5) ∧ p5) → p3) ∨ p5) → p4)) → False)) ∧ p1)) ∨ ((False ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860556883234286691002822857389 : (((((((((True ∨ ((p2 ∨ p2) ∧ True)) ∧ ((p5 ∨ True) ∨ p5)) ∧ p4) ∨ (p1 → p1)) → ((p3 ∧ p3) ∧ p4)) → (p3 ∧ p4)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((True ∨ ((p2 ∨ p2) ∧ True)) ∧ ((p5 ∨ True) ∨ p5)) ∧ p4) ∨ (p1 → p1)) → ((p3 ∧ p3) ∧ p4)) → (p3 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((True ∨ ((p2 ∨ p2) ∧ True)) ∧ ((p5 ∨ True) ∨ p5)) ∧ p4) ∨ (p1 → p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : ((((True ∨ ((p2 ∨ p2) ∧ True)) ∧ ((p5 ∨ True) ∨ p5)) ∧ p4) ∨ (p1 → p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45651028467058132265632082556 : (((p4 ∨ (True ∨ ((True ∧ (p5 ∧ ((((p1 ∧ p2) → ((True ∨ ((p4 ∧ True) → p4)) ∧ p1)) ∨ p3) ∧ (True → True)))) ∨ p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300397969176400673523170497153 : (False ∨ (((True ∨ True) → ((((p5 ∨ p4) ∧ (p2 ∨ p3)) ∨ (p1 → ((p4 ∨ (p5 → (p2 ∧ p5))) ∨ False))) ∨ True)) ∨ (p5 ∧ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451961223370146733124166997698 : ((((((p3 → False) ∨ p4) ∧ ((((p5 ∨ p2) → (((p5 → False) → False) ∨ (p3 → p3))) → False) → p5)) ∨ (p5 ∨ ((False ∨ True) → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310427207522134989884404491250 : (p2 ∨ ((((p2 ∨ p5) ∧ p5) ∧ (p5 ∧ (p2 ∧ p1))) → ((True → (p4 ∧ ((((True → p4) → ((p2 ∨ p1) → p3)) → False) ∧ False))) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247998731274703495471906186344 : ((p1 ∨ p4) ∨ (p2 ∨ ((((p2 ∨ p1) ∨ (True → p3)) ∨ (p4 ∧ ((p5 ∧ (False ∨ (p1 ∧ ((p2 → (False → p1)) ∨ False)))) ∨ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165637646657170463036875756772 : (((p3 ∧ ((True ∧ p2) ∧ (False ∧ p1))) ∧ (p2 → (False → (p4 → (p5 → (p1 ∧ p2)))))) ∨ ((p1 → (p3 ∨ False)) ∨ ((p3 ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190417734171039675186871236555 : (((p1 ∨ ((((p4 ∧ p4) → p3) ∨ p3) → p1)) ∨ True) ∨ ((True ∨ ((((p4 ∧ (False → (False ∧ p3))) → (p2 → p3)) ∧ True) → True)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48201447391409674887769090276 : ((((False ∧ p3) → (((p4 ∧ False) → (p1 ∧ p3)) → ((p4 ∧ ((((True ∨ False) → p1) ∨ (p2 ∧ p4)) ∨ p3)) → p3))) → (p1 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53730051814602282441733483702 : (((p1 → (False ∧ (((p3 ∨ (False ∨ True)) ∨ p1) → p3))) ∧ ((p4 → p3) ∧ ((p1 ∨ (p1 ∧ p5)) → (((p1 ∧ p3) ∨ p2) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329608539106615817290075602017 : (True → ((p3 → False) ∨ (p1 ∨ ((p2 → ((p1 → p3) ∨ (((((p3 → (p5 ∨ (True ∨ False))) ∨ p5) ∧ False) ∨ (p2 → True)) ∨ False))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87200269093767838865729739561 : (((p4 → ((True ∧ ((p5 ∨ p5) ∨ False)) ∨ True)) → (((((p4 ∨ p3) ∨ ((p5 ∧ True) ∧ (p4 ∨ p5))) ∧ p2) ∧ (p3 ∨ p1)) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((True ∧ ((p5 ∨ p5) ∨ False)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149401203274769233816837429755 : ((True ∧ (((((p4 ∨ ((p1 → ((True ∧ ((p2 ∨ p5) ∧ p4)) ∨ p3)) → True)) ∨ False) ∧ p5) → p5) → p4)) ∨ ((p4 → True) ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800872796329268818509739244279 : (((p2 → ((p1 ∧ (((False → p2) → (((p2 ∧ p2) → ((p5 ∨ (p5 → p5)) ∨ False)) → p4)) ∧ ((p3 ∧ True) ∨ p1))) ∨ (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457447165955309541061216103091 : (((((((p1 ∧ (((True ∨ p5) ∨ (p3 → p2)) ∧ True)) → p4) ∧ ((p3 → p5) → p2)) → p4) ∨ ((p3 ∧ p5) → ((True → p3) ∨ p1))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165249770673004627597669897355 : (((True → ((p4 ∧ p3) ∨ (p4 ∧ (((p3 ∧ p3) ∨ p5) ∧ (p4 → True))))) ∨ (p3 ∧ p2)) ∨ ((p1 → p4) → (((p3 → p5) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246633734722629045342533922481 : ((p5 ∧ p3) ∨ (((p4 → p3) ∧ (p3 → ((((p3 ∧ (False → p2)) ∨ p5) ∨ (p4 ∧ p4)) ∧ (p1 ∨ (p2 ∨ p4))))) ∨ (p1 → (False → p2)))) := by
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
theorem thm_5_vars_150256397655046326913255401069 : ((p3 → ((p2 ∨ (p3 ∨ (False → ((p1 ∧ p2) → p2)))) → (((p1 ∧ (p5 ∧ p2)) ∨ (p4 ∧ p4)) ∨ p3))) ∨ ((p4 ∧ False) → (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199309292021419451027739906834 : (((((p1 ∧ p2) → (p1 ∨ True)) ∨ True) ∨ p2) → ((((((((p3 ∧ p5) → p1) ∧ p2) → True) → p3) → (p3 ∧ (p5 ∧ p2))) ∨ p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668308135851709355418351964462 : ((((p4 → (((p3 ∨ ((p1 ∧ (False ∨ p5)) ∨ (False → p1))) ∧ p5) → ((((p5 ∨ True) ∧ p3) ∧ True) ∧ p3))) ∧ (p2 ∧ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119307796326554213414979080307 : ((p3 → ((p4 ∨ (True ∧ ((False ∨ p1) ∨ (((p2 ∧ (p2 ∨ (p5 ∧ (p5 → p2)))) ∧ p1) ∨ (False ∨ True))))) ∨ (p2 → p2))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357878845193431186318010010406 : (p5 → (p5 ∧ (((((p3 ∨ p3) ∨ True) ∧ p2) → False) → ((p2 → ((p3 ∧ (p3 ∨ ((((True ∨ p5) ∧ p4) → p4) → True))) ∧ p3)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133707798576216670066674128835 : ((((((p5 ∨ p5) ∨ (False → p5)) ∧ (p2 ∨ ((p4 → (p2 ∨ p5)) → False))) ∨ (p5 ∨ ((p3 ∧ p5) ∨ p1))) ∧ p2) ∨ ((p5 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320483832083153735395737746304 : (p4 ∨ ((p3 → p4) → (p2 → (((False → True) ∧ (((p1 → ((True → p4) ∨ p1)) → False) ∧ p2)) → ((p4 ∧ True) → (p1 → (p1 → False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (p1 → ((True → p4) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306678586793794535726506946232 : (p1 ∨ (True ∧ (p1 ∨ (p5 ∨ (((((p4 → p3) ∧ ((p3 ∨ (False ∨ p5)) ∧ (False ∧ p4))) ∧ (p4 ∧ p4)) ∨ (p2 → (p2 ∨ p1))) ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585817075684059875957127912666 : ((((((p2 → (False ∧ ((False ∨ True) → (p5 ∧ (((p2 → (((True → p5) ∨ p5) ∧ (p4 ∧ p1))) ∧ False) ∧ p4))))) → p3) ∧ p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171512733592153018867388925125 : (((((((p2 ∨ p2) ∨ p3) → False) ∨ (p3 ∧ ((p2 → True) ∧ p5))) ∧ True) ∨ p4) ∨ ((True ∧ ((True ∨ (True ∨ p4)) ∨ (p2 ∧ p2))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309647588499381781552694458943 : (p2 ∨ ((p1 ∧ ((False → (False → p3)) → ((((True ∨ (False ∧ p1)) → (p1 ∨ p2)) ∨ (p5 → p5)) ∨ (False ∧ True)))) ∨ ((False ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_135616240954287884737839977655 : (((p3 ∨ (((True ∨ ((((False ∧ p1) ∧ False) → True) ∨ p4)) → False) ∨ (p1 → p4))) ∨ (p4 ∨ (False ∧ (p2 → p3)))) ∨ (True ∨ (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157018402072919179595020875134 : ((((p3 ∧ p4) ∧ (((((((p1 ∧ p5) → (p3 ∨ True)) ∧ p4) → p2) ∨ p2) ∧ p1) ∨ p2)) ∨ p5) ∨ ((((p5 ∧ p4) ∧ False) ∧ p1) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148974436460315495014484424013 : ((((p2 → p3) → p3) ∧ ((p4 ∧ (p2 ∨ p4)) ∧ ((p2 → ((p5 ∧ p2) → (False ∧ p5))) → (True ∧ p2)))) ∨ ((False ∧ p1) → (p5 → p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177830877985270714972991933409 : (((((True ∧ (p2 ∨ ((p5 ∧ p3) ∨ (p3 → p2)))) ∧ p5) ∧ False) ∨ True) ∨ (p4 ∨ ((True → ((p1 ∧ p3) ∨ (p4 → (p5 → True)))) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150086217816013951222647295600 : ((True → (p3 ∨ ((p5 → (((False ∧ p5) → p5) ∧ p5)) ∧ ((((p5 ∨ (p5 ∧ p2)) ∧ p5) ∨ False) ∨ p4)))) ∨ (True ∨ ((True ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186567061185124403052956161514 : (((p1 ∨ (((p1 ∨ p5) ∧ p5) ∨ (p4 ∧ p3))) ∨ (p1 ∨ p3)) → (True → ((p3 ∧ p4) ∨ (((False → ((True → False) ∧ p5)) ∨ p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h15
          -- False on the left can always be used.
          apply False.elim h15
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h22
      -- False on the left can always be used.
      apply False.elim h22
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134245278384454167604404001207 : ((((True → (p4 ∧ (False → False))) → ((p3 ∨ True) → (((((p5 ∧ p5) → (p4 ∨ p5)) ∧ p2) ∧ False) ∧ p2))) ∨ True) ∨ ((p3 ∨ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148779637700401815063709173582 : ((((p2 ∧ p3) ∧ ((p1 ∨ p1) ∧ False)) ∨ (False → ((p2 ∨ p5) → (p1 ∨ (((p2 ∧ p2) ∧ p3) ∧ p1))))) ∨ (((True ∨ True) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52248249769673454363257891673 : (((False ∨ ((p3 ∨ (p3 ∧ ((p2 ∨ ((p3 ∧ (p1 ∨ p4)) ∧ p2)) ∨ p2))) ∧ p2)) → ((((p5 ∨ p5) ∨ p3) ∨ (False → p3)) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h13.left
          let h16 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119399459545999463869202758944 : ((p4 → (((((p1 ∨ (True ∨ (p4 ∧ (p2 → ((False → False) → p4))))) ∨ True) → ((p1 ∨ p3) ∨ (p4 ∧ p5))) ∨ p4) ∨ True)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64532214581732650311626519949 : ((p1 ∨ (((p3 ∨ (p1 → p1)) ∧ ((p3 ∨ True) → p2)) ∨ (p1 ∨ (((((True → p3) ∧ p2) ∨ p2) ∨ p4) ∨ (p4 ∧ (p3 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258600090677565981824217152366 : ((p5 ∨ p4) → ((((p1 ∧ (((p3 ∧ (False ∧ (True ∨ p1))) → p5) ∨ (True ∨ p5))) ∧ (p2 → p3)) → p5) → ((True → (p3 ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381838456256464771828593419118 : ((((((p5 ∧ ((((False ∨ p1) ∧ True) ∧ ((((True ∨ True) ∧ (p1 ∧ p5)) → (p5 → p1)) → (p4 → False))) ∧ p4)) ∨ p2) ∨ p3) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672603353928187077821200511736 : (((((False ∨ (p3 → (((False ∨ p3) ∧ p1) → ((p4 → p5) ∨ ((p4 → p3) ∨ (p4 → p2)))))) ∧ (p4 → p4)) → (False ∧ (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149879574864755374782482645331 : ((p2 ∨ (((True ∧ (False → p2)) ∧ ((p1 → ((False ∨ True) → p5)) ∨ p1)) → (((p3 ∧ True) ∧ p5) ∧ p2))) ∨ ((False → False) → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147679983209261441671161589391 : ((((p2 ∨ (p1 → (p5 ∨ ((p2 ∨ p3) ∧ (((p3 ∧ p3) ∧ p3) ∨ p4))))) ∧ (True → (True → p2))) → p5) ∨ ((p2 → (p3 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302819982283208680047516830019 : (False ∨ (p5 ∨ ((((p4 → (True → p3)) → ((((p5 ∨ (False ∨ p1)) ∨ p3) → p3) → p3)) ∨ True) ∨ (p1 ∨ (((False ∨ True) ∨ p4) → p3))))) := by
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
theorem thm_5_vars_53386320451980232495401880761 : ((((p2 ∧ ((p4 ∨ ((False → (p1 → p1)) ∨ p4)) ∨ p3)) → False) → (p2 ∨ ((p4 ∧ (p4 → (p5 ∧ (p4 → p3)))) → (False ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177628247659608436560682365232 : ((((((False ∨ p1) → (p3 → ((p5 → p4) ∧ False))) ∨ p3) ∧ p4) ∧ p2) ∨ ((True → (p1 ∨ ((p5 ∨ (p4 ∨ (p1 ∨ p4))) ∨ True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209060931981305468579870483128 : ((p1 ∨ ((p3 ∧ p5) → (p3 → p4))) → (p5 → ((True → (((True → p4) → False) ∧ (p3 ∧ p4))) ∨ ((p3 → p3) ∧ ((p2 ∨ p4) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346818153702289561002972041137 : (p3 → (((((p1 ∨ p2) ∨ (p4 ∧ ((p3 → (((p1 → p5) → p3) ∨ p5)) → p4))) ∧ (p3 → False)) → p4) → ((p2 ∨ (p3 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217333079882401450745448146714 : (((p1 ∨ (True ∧ p1)) ∨ p3) → ((((p5 ∧ p4) → (((p4 ∧ p2) ∧ p1) ∧ ((p2 ∨ p3) ∨ ((True → p2) ∨ (p5 ∨ False))))) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_4460456581992736035970843171 : (p2 → ((((((p1 ∨ (p3 → p1)) ∨ (False ∧ (True → ((False ∧ True) ∨ p4)))) ∨ (True ∧ p3)) ∧ (p4 ∨ p5)) → p5) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_774195644310618131170641662163 : (((False ∨ (((p3 → (((p1 ∧ (True ∨ (p2 ∧ ((p3 → p4) ∧ p5)))) ∨ p1) ∨ ((True ∧ p4) ∨ p3))) ∨ p1) ∧ (p1 ∨ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183792551227943815560485748953 : (((((p4 → ((p1 ∧ p2) ∨ (p1 ∧ p3))) ∧ False) ∨ False) ∧ p1) ∨ ((((((p5 → p2) → p2) ∨ p2) → p4) ∧ (p4 ∧ (p3 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191542902545940189902528428805 : ((p1 ∧ ((p3 ∧ ((p1 ∨ p3) ∧ p3)) ∧ (True ∧ p4))) ∨ (((False ∨ p5) ∨ ((p5 ∧ ((p3 ∧ p1) ∨ True)) ∨ p5)) → ((True ∧ p1) → p1))) := by
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
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731874647722790927761744735691 : ((((p4 → (p2 → p2)) → (((p5 ∧ p2) ∧ (p1 ∨ ((True → ((p1 → (False → ((p2 → p4) ∨ p5))) → False)) ∧ (p5 ∨ False)))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_318924449919905531284095851528 : (p4 ∨ (((((((p2 ∨ (p3 → p3)) ∨ (p5 → p5)) → (True ∧ (p2 ∨ (p5 ∨ p4)))) ∧ p4) ∨ (p2 → p3)) → False) → (p5 → (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((((p2 ∨ (p3 → p3)) ∨ (p5 → p5)) → (True ∧ (p2 ∨ (p5 ∨ p4)))) ∧ p4) ∨ (p2 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47602521190884212545950270956 : (((p3 → (False ∨ (False ∧ (False ∨ ((((p3 ∨ (False ∨ (p3 ∧ p1))) ∧ (p4 ∨ p1)) ∨ p5) ∨ ((p1 → p3) ∨ p2)))))) ∨ (False → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1560795383768077350193716059 : ((p5 ∨ ((((p2 → False) → (False ∧ (((p1 ∧ p5) ∧ (True ∨ (p1 ∨ p2))) ∧ p4))) ∧ ((p4 ∧ p2) → False)) → p5)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



