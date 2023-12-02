variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345358226807593881009240969248 : (p3 → ((((p4 → ((False → (p5 ∨ p1)) ∧ (((p4 → (((p4 → p2) ∨ p1) → (True ∨ True))) → (False ∨ False)) ∧ p2))) ∨ p2) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264150929696460895986983461005 : (True ∧ ((((p4 ∨ (p4 → p2)) ∧ (p3 ∨ p3)) ∧ p1) ∨ (((p1 ∨ (p2 → ((p5 ∨ p4) → True))) ∧ (p2 ∧ ((True ∧ p2) ∨ p4))) ∨ True))) := by
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
theorem thm_5_vars_717315066957825014276233407233 : ((((p4 ∨ (p4 → (p3 ∨ p5))) ∧ ((p4 ∧ (p3 ∨ True)) ∨ (((True → True) → p3) ∨ ((p5 → ((p3 ∧ False) → p2)) ∨ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58880466758080997432892283643 : (((False ∧ p1) ∨ ((((p2 ∧ p5) ∧ (p2 → p4)) ∧ p5) ∨ ((((p3 → (p4 → p4)) → p5) ∧ (p1 ∧ (p3 ∧ p4))) → (p3 ∨ p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135262050801030391416608550525 : (((p3 ∧ ((p1 → p2) ∨ ((((False → (p5 ∧ (p4 → p1))) ∨ (True ∧ (p5 → p3))) ∧ p3) ∨ p5))) → (p2 ∨ True)) ∨ (True ∨ (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244662075434327326649799134183 : ((False ∧ p5) ∨ (True → (((((p2 ∧ True) → ((p4 → p3) → True)) → p2) ∨ (p2 → True)) ∨ ((p1 ∨ (False ∧ (True → (p3 ∨ True)))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305240587710381972791164982358 : (p1 ∨ ((p2 ∨ ((p2 ∧ True) ∧ (p5 ∨ (p3 ∨ (((p2 ∨ (False ∧ p5)) ∨ (True ∨ (p3 ∨ True))) ∨ p2))))) → ((p2 ∧ (p4 ∧ p5)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h15 =>
              -- Conjunctions on the left can always be decomposed.
              let h16 := h15.left
              let h17 := h15.right
              -- False on the left can always be used.
              apply False.elim h16
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h20 =>
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
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134920001831606444104819928066 : ((((True ∧ (((p3 → (p2 ∨ ((False → p4) → (p2 → (p2 → p2))))) → (p4 → False)) → p3)) ∨ p2) ∧ (p1 ∨ p3)) ∨ ((True → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197123750172156362095686454126 : (((p3 ∨ (((p2 ∨ p4) ∧ True) ∧ False)) ∨ p5) ∨ ((False → ((p4 → ((p3 → p1) ∨ (((p2 ∧ True) ∧ p5) ∨ (p1 ∧ p4)))) ∧ p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808865736224982328465317505187 : (((p5 → (((((True → (p4 → True)) → (False ∧ ((((p4 ∨ p2) → True) ∨ (((p2 ∨ p2) → p5) → p2)) ∧ False))) ∧ False) ∨ p5) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162480570726878715196278005818 : (((p1 ∧ (((False ∨ (p3 → (p5 ∨ (True → p5)))) ∨ ((False ∧ False) ∧ p5)) → p1)) ∨ True) ∧ (p4 → ((False → ((p1 → False) ∨ p1)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143951933953879872847806962651 : ((((p4 → (True ∨ p4)) ∧ (((p1 ∧ p3) ∧ (((False ∨ p4) ∧ p1) ∧ (p2 ∨ p1))) ∨ (p1 → p5))) ∨ True) ∧ (True ∨ ((p1 → True) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103032616108272168526528966821 : ((((((p3 → (p5 ∨ p4)) ∨ (True ∧ p1)) ∨ p1) → ((((False ∨ p1) ∨ p1) → (p2 ∧ p4)) ∨ (p3 → (False → p1)))) ∨ p5) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42300558094964712943052127449 : (((p2 ∧ (((p5 ∨ (p3 ∧ p1)) ∧ (p5 ∨ ((((p2 ∧ (((False → False) ∧ p5) ∨ False)) ∨ p1) ∨ False) ∧ True))) ∧ (p3 → p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256561881672838083789432912912 : ((False ∨ p5) → (p2 ∨ (((p3 ∨ (p5 ∧ True)) ∧ (True ∧ ((p2 ∧ (p1 ∨ p3)) ∧ True))) ∨ (p1 → ((p5 ∧ ((p5 → p2) ∨ p2)) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743703921393090722483586588876 : ((((True ∧ p3) → (((((p1 ∨ False) ∧ ((p1 → True) ∧ p4)) → p2) → (True → (p4 ∧ (p4 ∨ (p2 ∨ (p1 → (p1 ∧ False))))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62705124676504508589728982148 : ((p4 ∧ ((((False ∧ ((p5 ∨ True) ∧ (p5 → p4))) → False) → (False → ((p5 ∧ ((p4 ∧ False) → False)) → (p2 ∧ (p4 → False))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64492913020720638187536862533 : ((p1 ∨ (((((((True → True) ∧ p5) → p5) → False) ∧ ((p2 ∧ p2) ∧ (False ∧ p2))) ∧ p2) ∨ (((p2 → False) ∧ p2) → (True → False)))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40503235722124590558905477997 : ((((p1 ∧ ((p2 ∨ (((p3 → ((p3 ∧ p4) → (True ∧ p1))) ∨ (((p2 → True) ∨ False) → (False ∧ p4))) → p5)) ∧ p5)) ∨ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781796851853150349793577927304 : (((p2 ∨ (True → (((p5 ∧ (False → p3)) ∨ (((True → ((p3 ∧ p1) ∧ (p5 ∧ (p5 ∧ True)))) ∧ False) → p5)) → (p4 → (p1 ∨ p4))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61560084620071322195592684002 : ((p1 ∧ (((False → False) ∨ (p2 → ((p1 → p4) ∨ p3))) → ((p2 ∨ p3) ∧ ((p5 ∨ ((((p4 ∨ p2) → p4) ∨ p4) ∨ True)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198906908057242225358903842964 : ((p3 → ((False ∨ False) ∧ (p2 ∨ (p1 ∨ p5)))) ∨ (((((p5 ∧ p5) ∨ p4) ∨ (((p3 → p4) ∧ p3) → p4)) → ((p1 ∨ False) → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115402748182655982790149555679 : (((p1 ∨ ((((False → p3) ∨ True) ∨ p4) ∨ True)) ∧ ((p5 ∧ (p4 ∨ ((False ∨ False) ∨ (p5 ∧ (p4 → (p5 ∨ p1)))))) ∨ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300828515188828225565088905736 : (False ∨ ((p1 ∨ (p1 ∧ (((((p3 → (p5 ∨ p2)) → p3) ∧ p1) ∨ (p3 ∨ p4)) ∨ False))) → ((p3 ∧ ((p5 ∧ p5) ∧ p1)) ∨ (p4 ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191687529298198533539408900080 : ((p5 ∧ (p1 ∨ ((p5 → (p4 → p1)) ∧ (False ∨ p5)))) ∨ (False → ((p4 ∧ ((False → (p1 → (((True → p1) ∨ False) → True))) → False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258848074443632606652198337273 : ((True → p1) → ((p4 ∨ (False → (((p2 ∨ (p3 → p3)) → False) ∧ True))) ∧ (((((p4 → (False ∨ p3)) ∧ False) ∨ (True → p2)) ∨ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59911577892712778374176835829 : (((p5 ∧ p2) → (True → ((p4 ∨ p3) ∧ ((False ∨ True) ∧ ((p3 ∨ p1) → (((p1 ∨ (p4 ∨ True)) → (p1 → p4)) ∧ (p5 ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709719393804405018099665903114 : ((((True → ((p1 ∨ p5) ∨ (p3 ∧ (p1 → True)))) → ((True ∨ p2) → (((p3 → (True ∧ (p1 ∧ False))) → (p5 ∧ (p4 → p2))) ∨ True))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746522132963693125909935326422 : ((((p2 ∨ p4) → (False ∨ (((p2 ∨ (p1 ∨ False)) ∨ ((p1 → p4) ∨ (p4 ∧ (p3 → False)))) ∨ ((p2 ∨ (p5 ∧ (True → p5))) → p4)))) ∨ p1) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793217563722524909071773996074 : (((True → (p1 ∧ (((((p3 ∧ p1) ∨ p2) ∧ False) ∧ ((False ∨ (p2 → (((p2 ∧ False) ∧ (p2 → p3)) ∧ p4))) → (p1 ∧ False))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55178607191750599247623107903 : ((((((p5 ∧ p2) ∨ p5) → False) → p5) ∨ (((((True → True) → p2) → (((True → (True ∧ False)) → p3) → p3)) → p3) ∧ (p1 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258908122125611296410692705866 : ((True → p2) → (((True ∨ (((True → True) → (p3 ∨ (True → False))) ∨ p4)) → p3) → ((p2 ∨ p1) → (((p1 ∧ (True ∧ True)) ∧ p1) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (((True → True) → (p3 ∨ (True → False))) ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116346057152383123712764279400 : ((((p4 ∧ p5) ∨ True) → (p5 ∨ (((p4 → False) ∨ (True ∧ (p3 ∧ p5))) → ((p1 ∨ (p3 → (p3 ∧ (p2 ∨ False)))) ∧ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112670941779841168962032753161 : ((((((((((p1 ∨ True) ∨ p1) ∨ p4) ∨ ((True ∨ (p2 → p4)) ∧ False)) ∧ p5) ∨ True) ∧ p3) → (p3 ∧ (p5 ∧ p1))) → p4) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301591813386846673351790453939 : (False ∨ (((p1 → True) ∧ p5) → ((p4 ∧ ((p3 ∨ (p1 ∨ p1)) ∨ p2)) ∨ (True ∧ ((False ∨ ((p2 ∧ p4) ∧ (p3 ∨ p5))) → (p5 ∨ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801634280452912782846143163249 : (((p2 → ((p3 → ((True ∨ p1) → p3)) ∧ (p5 ∧ (((p1 ∧ p1) ∨ (p1 ∨ (p2 ∧ p3))) ∨ ((p4 ∨ p5) → ((False → p3) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70838319433220925042298252508 : (((((p4 ∨ (True → (((True ∨ p1) ∨ (p3 ∨ p5)) ∨ True))) → False) ∧ ((p4 ∨ ((p5 → True) ∧ p2)) → ((p2 → p3) ∧ p1))) ∧ p1) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ (True → (((True ∨ p1) ∨ (p3 ∨ p5)) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118236779431956827936030997076 : ((p1 ∨ ((p4 ∧ ((((p3 ∧ (((p2 ∧ False) ∨ ((p4 ∨ False) ∧ False)) ∧ p2)) → (True ∧ True)) ∧ (p4 ∨ False)) ∧ p4)) → p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64577868074136718494234123775 : ((p1 ∨ ((True ∨ (p2 ∧ p5)) → ((((((p5 → True) ∨ (p2 ∨ p5)) ∨ p2) → p3) → (((p5 ∨ (p5 ∧ p5)) ∧ True) ∨ p1)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723775457484940535390678901771 : (((((p2 → p2) → p4) ∧ (p3 → ((p5 → (((p5 ∨ ((p5 → False) → (p5 → (False ∨ p2)))) → False) ∧ p3)) ∧ (False ∨ (p2 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178282818111674664321433002013 : (((True ∧ (p5 → ((False ∧ ((True ∧ p4) ∧ True)) ∨ p2))) ∧ (p1 ∧ p3)) ∨ (((True ∧ p1) → (p1 ∧ p1)) ∨ (True ∨ ((True → p3) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158390275983025950062465690956 : (((p2 → p3) ∧ (False ∧ ((True → (((p5 ∧ (p2 ∨ ((p4 ∨ p4) ∧ p5))) ∨ True) ∧ p3)) ∨ p5))) ∨ (((True → p2) ∧ p1) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305868952190292155209736694216 : (p1 ∨ (((((False ∨ p2) → p1) ∨ p5) → p1) ∨ (p2 → (((((p4 → (p4 ∧ ((True ∨ False) ∨ p1))) → (True ∨ p2)) → True) ∨ False) ∨ True)))) := by
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
theorem thm_5_vars_322298132930609377576626124554 : (p5 ∨ (((((p1 ∨ (p2 → p4)) ∧ p4) → ((p4 ∧ p5) ∨ ((((p1 → (p3 ∨ p5)) → True) → (p2 → True)) ∧ (p4 ∨ p1)))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112605259512695148092420948031 : ((((((((p3 → p5) → (((True → False) ∨ p4) ∧ False)) ∨ p5) ∧ (((p5 ∧ p5) ∨ p4) ∨ p5)) ∨ p3) ∨ (True ∨ p2)) → False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158694977202468512066904151404 : ((p2 ∧ (p3 ∧ (p2 → (((p3 ∨ (p5 ∧ False)) ∨ (((False ∨ False) ∨ p1) ∨ (p4 ∧ p1))) ∧ p5)))) ∨ (p2 ∨ ((p4 ∧ p1) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_219388110713773971055176900075 : ((p3 ∨ (p2 ∧ (True ∨ False))) → (((((p4 → p3) ∨ p4) ∧ (False ∨ (p4 → p4))) ∧ (((((p1 ∨ True) ∨ p5) ∧ p3) ∧ p4) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_158114953360370710788182416395 : (((p2 ∧ (p1 ∧ (p3 ∨ p5))) ∧ (p4 → ((((p4 ∨ p3) ∧ p3) ∧ (p2 → (True → p2))) ∧ p4))) ∨ (False ∨ (True ∨ (p5 ∧ (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667952439265501446138759684980 : ((((p3 ∨ (((p5 ∨ (p2 → ((((p5 ∨ p3) → p3) ∧ (True ∧ (True ∨ p3))) ∨ p1))) ∨ True) ∨ (p1 → True))) ∧ ((p4 → False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353543624390509417144261682603 : (p4 → (p3 ∨ ((p1 → ((((p3 → True) → ((True ∨ p5) → (p4 → p2))) ∨ p4) ∨ ((p2 ∧ p3) → ((False → p3) ∨ p4)))) ∧ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637560238221206094331332909750 : (((((((p4 → (False ∨ (p2 ∨ p1))) ∧ False) ∨ (True ∨ p5)) ∨ ((p2 → (p4 ∧ ((((p5 ∨ True) ∧ p3) ∨ p1) ∨ p4))) → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135443222681143839832820255180 : ((((((((((False → True) → p1) ∨ p2) → True) ∧ p1) ∧ (p1 → p4)) → (p3 ∧ p4)) ∧ p1) → ((p5 → p4) → p4)) ∨ (True ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663831792765584932371522341422 : ((((p3 ∧ ((((p5 ∧ (((p2 → p1) ∧ p1) → (p5 ∨ p5))) ∧ (False → ((p5 → (p1 ∧ p5)) ∧ False))) → p4) ∨ p1)) → (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807523217060071514847198917878 : (((p4 → ((p2 ∧ (((p1 ∧ p4) ∧ p2) ∧ True)) ∨ (p3 ∨ (p3 ∨ (p4 ∨ ((True → (p2 → p3)) ∨ (((False ∧ p5) → p1) ∨ p5))))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67855349507330179777714491557 : ((p2 → ((p2 ∧ (((p3 ∨ (p3 ∧ ((False ∨ p5) → True))) → ((False ∨ (p2 → True)) → (False → True))) ∨ (p4 ∧ p4))) → (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765336482124571839018213677525 : (((p4 ∧ ((p1 ∧ ((((False → p5) → p5) ∨ p1) ∧ (p3 → ((((False ∧ p3) → p3) → (p4 ∨ True)) ∨ p1)))) ∨ (p4 ∨ (p5 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112685062010311559730036369835 : (((((((p5 ∨ (p1 ∧ (p1 ∧ ((False → (p5 → p3)) ∧ p2)))) ∨ p3) ∧ True) → p2) ∧ (((p5 ∨ p5) ∧ True) ∨ p3)) → p2) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (((p5 ∨ (p1 ∧ (p1 ∧ ((False → (p5 → p3)) ∧ p2)))) ∨ p3) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (((p5 ∨ (p1 ∧ (p1 ∧ ((False → (p5 → p3)) ∧ p2)))) ∨ p3) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (((p5 ∨ (p1 ∧ (p1 ∧ ((False → (p5 → p3)) ∧ p2)))) ∨ p3) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777051752505240762682685026782 : (((p1 ∨ (((p2 → ((False → (p5 → p1)) ∧ p4)) → (True ∧ (p4 ∨ (((p4 ∧ (True → p4)) ∧ (p3 ∧ False)) ∨ p4)))) ∨ (p4 → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_121727770425951165602525268419 : ((((((p4 → (True ∨ False)) ∧ p4) ∨ p5) ∨ ((False ∧ p2) → (False ∧ ((p3 → p5) → (p4 ∨ ((p1 ∨ p1) → p4)))))) → p3) → (p4 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → (True ∨ False)) ∧ p4) ∨ p5) ∨ ((False ∧ p2) → (False ∧ ((p3 → p5) → (p4 ∨ ((p1 ∨ p1) → p4)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392584850654612834945571027932 : (((((p3 ∧ (p2 ∨ p5)) ∨ (((p2 ∨ True) ∨ (((True → p2) ∧ p3) → p3)) ∧ (((p1 → p2) ∧ (p2 ∧ p3)) → (p2 → p4)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_149108307352661430009486219263 : (((p3 → (p2 → False)) → (False ∨ (((((p3 ∨ (p1 ∨ p1)) ∧ p3) → False) ∨ p3) ∨ (p3 ∧ (False ∨ p1))))) ∨ (((p3 ∨ True) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244757596507566635018019909996 : ((p1 ∧ False) ∨ (((p3 → ((((p2 ∧ p2) ∧ False) → p2) ∧ (p5 ∧ p2))) ∧ p3) ∨ ((True ∧ p4) → ((p1 ∧ ((True → p2) → p2)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337898003415784293753827372721 : (p1 → (((p3 → p4) ∨ ((p3 → ((p5 ∧ ((p1 ∧ p4) ∨ p5)) ∧ p1)) ∧ True)) → (p2 → (p3 ∨ (p5 → ((p2 ∧ (p5 → p3)) ∨ p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166768534759188774677674984218 : ((p5 → ((p5 ∧ ((p1 ∧ ((p4 → False) → p5)) ∧ (p3 ∨ (p2 ∨ (p2 ∧ p4))))) ∨ p4)) ∨ (((p5 ∧ (p3 → p3)) ∨ (p5 → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51862077442582693949022349699 : ((((((p3 ∨ ((p1 → p3) ∧ (True ∨ ((p4 → False) ∧ p3)))) ∨ p4) → False) ∨ p1) ∨ ((((p5 → p3) ∨ True) ∨ (p5 ∨ p4)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652254676877835258881880504194 : ((((p3 ∧ ((((p5 ∧ p5) ∧ True) ∧ ((((((p3 ∧ p4) → (True ∨ True)) → p4) ∨ p5) → p2) ∨ (p4 → p5))) ∧ p1)) ∧ (p2 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42393879421737163880261906658 : (((p4 ∧ ((p5 → p2) ∧ (((p3 → (((p4 ∨ p4) ∧ p3) ∨ False)) → (((p1 ∧ (p2 ∨ p1)) ∨ p2) ∨ p5)) ∧ (p1 → p3)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252946014614306279691946903974 : ((True ∧ p2) → (((True ∨ True) ∧ (((True ∧ (p4 ∨ (True ∧ p4))) ∨ (p5 ∧ p5)) ∧ (((p1 → p1) → (True ∨ True)) → p5))) ∨ (True ∨ p3))) := by
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
theorem thm_5_vars_65000062899708434461595747451 : ((p2 ∨ (((p3 ∧ p3) ∨ p2) → ((((p2 ∨ ((p5 ∨ p3) → ((p4 ∨ True) ∧ (p5 ∨ p5)))) ∨ (True → (p2 ∧ p5))) ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353500690958879639327888523765 : (p4 → (p2 ∨ (((True ∨ p5) ∨ (False ∧ p4)) → (((p2 ∨ p1) ∧ ((p2 → p1) → p4)) → ((p3 ∧ ((p1 ∨ (True → p5)) ∨ False)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115945754330516765986401613358 : (((p3 ∨ ((p4 ∨ p4) ∨ False)) ∨ ((True ∧ p4) ∨ (((((((p1 ∧ p5) → True) → p3) → (p1 ∨ p4)) ∨ False) → True) ∨ p5))) ∨ (True ∧ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64494690201441981704613628714 : ((p1 ∨ (((((p5 → p1) → p5) ∨ p2) ∨ (False → ((p1 ∨ (p2 → (True ∧ p5))) → True))) ∨ (p3 → (((False ∨ p3) → True) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48874572142687700042240807025 : (((True → (((False ∧ (((p2 ∨ p3) → ((p2 → (True ∨ False)) ∧ p5)) ∨ p3)) ∧ True) ∧ ((p1 ∨ p2) ∧ True))) ∧ (p2 ∨ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159172889479656244631872194260 : ((p1 → ((((p5 ∧ p3) ∨ p3) → True) → ((((p3 → p3) ∧ p3) → (True → (p2 ∧ p4))) → p3))) ∨ ((False ∧ p2) → ((p4 ∧ p5) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244130494378530667834695057900 : ((True ∧ p4) ∨ ((True ∧ (p3 → (p3 ∧ (p4 ∨ ((((p3 ∧ p5) ∨ (p5 → (False ∧ (p4 ∨ ((p1 ∧ False) ∧ p5))))) ∨ True) ∨ True))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_174543102833309109667687578791 : (((p1 ∨ ((p2 ∧ (p1 → p1)) ∨ False)) → (((p4 → p5) ∨ True) ∨ (p3 ∧ p4))) → (p5 → (((p5 ∨ p5) → ((False ∨ p1) ∧ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217223546396864784493874561242 : ((((p3 → False) → p3) ∨ p3) → ((p4 → (((p3 ∨ p5) ∨ p4) ∨ False)) → (True → (False ∨ (p3 ∨ (((True ∧ p4) ∨ p4) ∨ (False → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249548966467331602363953778992 : ((p5 ∨ p2) ∨ ((p4 ∨ (True → (((p1 → (p1 → True)) ∧ ((p1 ∨ p3) ∧ p5)) ∨ (p3 ∧ (p5 → (p4 ∧ p5)))))) ∨ ((False ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69041037855701635483882116797 : ((p5 → ((((((p3 ∧ ((False ∧ False) ∨ p5)) ∨ p1) ∨ p4) ∧ p2) ∨ ((p2 ∧ (p2 ∧ True)) ∧ (((False ∧ True) ∧ p5) → False))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315882762663824563864094167912 : (p3 ∨ (True ∧ ((p1 ∧ (True → (False ∨ ((p3 ∧ False) ∧ ((p5 ∧ (p5 → p3)) → (p3 → (p2 → ((True ∨ (False ∧ False)) ∧ False)))))))) ∨ True))) := by
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
theorem thm_5_vars_762880852521295542940902332539 : (((p3 ∧ ((((p4 ∧ p1) ∧ p5) → (False ∧ p2)) ∨ ((((p2 ∨ p2) → ((False ∨ p5) ∨ (False → p5))) → ((p1 → p4) ∧ p3)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37252479426393372785129643892 : ((((p1 ∧ (((((p5 ∧ (p3 → (((p5 → (p1 ∨ p5)) ∨ p2) ∧ p1))) ∨ p5) → p1) ∨ (False → (p4 → p4))) → p5)) ∧ p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807977369264269878031281545608 : (((p4 → ((p3 ∨ p3) → ((((((p2 ∧ p3) ∨ False) ∨ (p5 ∨ p3)) ∧ (p5 ∨ (True → (((p2 ∧ p5) ∨ p3) ∨ p5)))) → p1) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183611432035317683080801751424 : ((False → (p5 ∧ (True → ((((p4 ∨ p5) ∨ False) → False) ∨ True)))) ∧ (((p2 ∧ ((False ∨ (p5 ∧ p3)) ∨ (p4 ∧ p1))) ∧ p4) ∨ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775400158045254994958635616260 : (((False ∨ (p2 ∧ ((p1 → (p5 → ((False → ((((p2 → p2) ∧ (True → (p5 → p5))) ∨ p1) ∧ ((True ∨ p2) ∨ p2))) → p3))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215566629442068091638842740590 : ((p5 ∧ ((False → p3) ∨ True)) ∨ ((((True → p1) ∧ (True → False)) ∧ ((((p4 ∧ (p5 ∨ (p3 → p4))) ∧ False) → p1) ∨ (True ∧ p1))) → p2)) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667381342849109607726342362832 : (((((p1 ∧ p1) → (((p2 ∨ ((((p1 → (True ∧ p5)) → p1) → (False ∧ p3)) ∨ p3)) ∨ p2) ∧ (p4 ∨ p3))) ∧ (False ∨ (p3 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115129215988316402113606081563 : (((((False → True) ∨ (False ∧ False)) → (((False → p1) ∧ True) ∧ True)) → (True ∧ (False ∧ ((p2 → ((p3 ∧ p4) → p3)) ∧ p2)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302605488736170975436510491755 : (False ∨ (p1 ∨ (True → (((((((p2 → True) ∧ p1) ∨ ((p2 ∨ p1) ∧ (p1 ∧ True))) ∨ (p5 → (p4 → p2))) → (True ∧ p2)) ∨ False) ∨ True)))) := by
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
theorem thm_5_vars_115183365979414821622635693686 : ((((p3 ∧ (True ∨ (p5 ∨ (p4 ∨ p3)))) ∨ (p4 ∨ False)) ∧ (p1 → (True ∧ ((p1 → (p2 → ((p1 ∧ True) → False))) ∨ p4)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58376989292354745157165193166 : (((p1 ∨ p3) ∧ (((p2 → (((p2 → p3) → (((p3 ∧ (True ∨ True)) ∨ p4) → (p1 ∨ (p4 ∧ p5)))) → (p5 ∨ p3))) ∧ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197250429489779206933849555230 : ((((p1 ∧ ((p5 ∨ p3) ∧ p5)) → p4) → p3) ∨ ((p5 ∨ (((p2 ∧ True) ∧ False) ∨ True)) ∨ (((p4 ∨ (p2 ∧ p3)) ∨ p5) → (False ∨ p5)))) := by
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
theorem thm_5_vars_63994701841168363143732670614 : ((False ∨ ((p4 ∨ (False → (p4 ∨ (((((((p1 ∨ True) ∨ p2) ∨ (p4 ∧ (p3 ∨ True))) ∧ (p4 → p5)) ∨ p4) ∨ True) ∧ p5)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773519434869897865908215307536 : (((False ∨ (((((((p1 → (p2 ∧ p5)) ∧ True) → ((p2 ∨ p4) → (p4 ∨ p3))) ∨ p4) ∧ True) ∨ (((p2 → p2) → p5) ∨ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202626081296011136380066245833 : ((((p5 ∧ p5) ∨ True) → (False ∨ True)) ∧ ((((False → ((p4 ∨ p4) → False)) ∧ p3) → ((False ∧ p3) ∨ p4)) ∨ (True ∨ (p1 ∨ (False ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63976312805963536128494657761 : ((False ∨ (((True → (False → ((True → False) ∧ (p3 → (((True ∨ (p4 ∧ True)) ∨ p3) → p1))))) ∨ (True ∧ ((False ∧ p4) ∨ p1))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130182946824504315121329971254 : (((p3 ∨ (((p1 → (((p5 ∧ ((p2 → False) ∧ (False ∧ p1))) → True) → (p2 ∨ p4))) → p4) ∧ p1)) ∨ (p1 ∨ True)) ∧ (True ∨ (p2 ∨ p1))) := by
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
theorem thm_5_vars_305503855310247769960066231438 : (p1 ∨ ((((p1 ∧ True) ∨ p5) ∨ ((True ∧ p1) ∨ (p3 ∨ ((p5 → True) → p1)))) ∨ (True ∨ (p4 ∧ ((True ∧ (p4 → p5)) ∨ (p4 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216653575454413704638825267554 : ((((p2 ∨ True) ∨ p3) ∧ p2) → ((False ∨ ((p1 → (False → p5)) ∧ ((p2 ∨ p5) ∨ (False ∧ p2)))) → ((p4 ∨ (p2 ∨ p1)) ∧ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h1.left
        let h10 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h25 =>
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h32
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h1.left
        let h39 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h42 =>
            -- One of the premise coincides with the conclusion.
            exact h39
        case inr h43 =>
          -- One of the premise coincides with the conclusion.
          exact h39
    case inr h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h44.left
      let h46 := h44.right
      -- False on the left can always be used.
      apply False.elim h45
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h47 =>
    -- False on the left can always be used.
    apply False.elim h47
  case inr h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h1.left
        let h54 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h55 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h56 =>
            -- One of the premise coincides with the conclusion.
            exact h54
          case inr h57 =>
            -- One of the premise coincides with the conclusion.
            exact h54
        case inr h58 =>
          -- One of the premise coincides with the conclusion.
          exact h54
      case inr h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h1.left
        let h61 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h62 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h63 =>
            -- One of the premise coincides with the conclusion.
            exact h61
          case inr h64 =>
            -- One of the premise coincides with the conclusion.
            exact h61
        case inr h65 =>
          -- One of the premise coincides with the conclusion.
          exact h61
    case inr h66 =>
      -- Conjunctions on the left can always be decomposed.
      let h67 := h66.left
      let h68 := h66.right
      -- False on the left can always be used.
      apply False.elim h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54762694961195103328076070058 : ((((p3 ∧ p3) → ((p5 ∨ (p1 → p2)) → p5)) → ((p2 → p2) → (p5 → (((p3 ∧ (p4 ∨ (p2 → (False ∧ p4)))) ∧ p5) ∨ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



