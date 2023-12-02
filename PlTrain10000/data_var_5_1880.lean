variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262416941417863163941273025272 : (True ∧ ((p1 ∧ (((p5 ∨ ((p2 ∧ ((p5 ∧ ((False → p2) ∨ p4)) ∨ p4)) ∨ True)) ∨ ((p5 ∨ True) ∧ (p5 ∨ p5))) → (p1 ∨ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323909611083715661000002297991 : (p5 ∨ ((p5 ∧ ((((p5 ∧ (p4 ∧ ((p2 → p1) ∨ p5))) ∨ True) ∧ (p2 ∧ True)) ∧ p3)) ∨ (p3 → (((p2 → (p4 → p4)) ∨ p3) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713704164725338184555836007770 : (((((p5 ∧ (p2 → (p1 ∨ True))) ∧ p5) → (p2 → ((((True → True) → (p1 ∧ (p2 ∨ (p3 ∧ p2)))) ∨ (p1 → (False → False))) ∧ p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201266456785120787553169518965 : ((p3 → (True ∧ (((p1 → p5) ∧ p3) → p5))) → (((((True ∨ p2) ∨ p1) ∨ True) ∧ ((p1 ∨ p3) ∨ p2)) → (p4 ∨ (p3 → (p3 → p3))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- Implications on the right can always be decomposed.
            intro h11
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- Implications on the right can always be decomposed.
            intro h14
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Implications on the right can always be decomposed.
            intro h22
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- Implications on the right can always be decomposed.
          intro h28
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Implications on the right can always be decomposed.
          intro h33
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Implications on the right can always be decomposed.
          intro h36
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- Implications on the right can always be decomposed.
        intro h39
        -- One of the premise coincides with the conclusion.
        exact h38
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h46
        -- Implications on the right can always be decomposed.
        intro h47
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h48 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h49
      -- Implications on the right can always be decomposed.
      intro h50
      -- One of the premise coincides with the conclusion.
      exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116783124746563029752005852396 : (((p1 ∨ p1) ∨ ((((((((p3 ∧ p5) ∨ p2) → False) ∨ True) ∧ p2) → True) ∧ (p1 ∨ (p2 ∨ ((False ∧ p5) → True)))) → False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46407440748654764814848766716 : ((((False ∧ (((p4 ∧ p3) ∨ (p4 ∨ p4)) ∨ False)) ∨ ((p1 ∧ (False ∧ (((p4 ∧ p4) ∨ False) → p5))) ∧ (True ∧ True))) ∧ (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258356607587452667777270826009 : ((p5 ∨ False) → ((((p4 ∨ True) ∧ (((False ∧ ((False ∧ p5) ∧ False)) ∨ p3) ∨ (True → False))) ∨ (False → p2)) ∨ ((p5 → p5) ∧ (p3 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80911627689461484509673465011 : ((((((((p5 ∧ p1) ∨ p2) → (p2 ∧ ((p1 → False) → p5))) ∧ ((False ∨ (True ∨ p2)) → False)) → p4) → p2) ∧ (p5 → (p2 ∨ True))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p5 ∧ p1) ∨ p2) → (p2 ∧ ((p1 → False) → p5))) ∧ ((False ∨ (True ∨ p2)) → False)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ (True ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45539158437177129003685642873 : (((p1 ∨ (p4 → (((((False ∧ False) ∧ p2) → (p3 → (True ∨ ((p5 ∧ True) ∧ ((False → p3) ∨ (False ∧ p3)))))) ∧ p4) ∧ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110797784733461789085349225817 : ((((((p1 → ((True ∨ p2) ∧ (p5 → ((False → p2) ∨ True)))) ∧ (p1 ∨ (False ∧ (p5 ∨ p4)))) ∨ (True → True)) ∨ p3) ∧ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228161781195041860796274367923 : ((p5 ∧ (True ∧ p2)) ∨ ((((False ∨ (p3 → (p5 ∧ p3))) ∨ True) ∧ (p2 → p4)) → (p2 ∨ ((p4 → (p5 ∨ p4)) ∨ (p2 ∧ (p1 → p3)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111890283894389802525880162250 : ((((p4 ∨ (False ∨ ((p3 ∨ ((p1 ∧ p4) ∨ (True ∨ (p2 → p1)))) ∧ True))) ∧ ((False → ((True → p1) ∨ p2)) → True)) ∨ p4) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322354986798386090089223062683 : (p5 ∨ (((((((True ∨ (p2 ∨ ((False ∧ p3) ∨ (False ∨ p3)))) ∧ (p3 ∧ (p1 ∧ p3))) → False) ∨ p5) → p1) ∨ ((p4 → p4) ∧ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_75745479339188524415072426103 : (((((p2 → (((p4 → (p5 ∧ (p3 ∧ False))) ∧ ((p1 → (p1 ∨ (p3 ∧ p5))) → True)) ∧ False)) → (p1 ∧ (p4 ∧ False))) ∨ True) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → (((p4 → (p5 ∧ (p3 ∧ False))) ∧ ((p1 → (p1 ∨ (p3 ∧ p5))) → True)) ∧ False)) → (p1 ∧ (p4 ∧ False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180782954138919764080885867715 : ((((p4 → p3) → (p5 ∧ p1)) → (p3 ∨ (p3 → (p2 → (p1 → False))))) → (p5 → (p5 ∨ (((p1 ∧ p3) ∨ False) ∧ (p1 ∧ (p1 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180353638581455527443639999900 : (((((p1 ∧ p2) ∨ (((p2 ∧ True) → p4) → p3)) ∧ True) ∨ (p5 ∧ p5)) → ((((p5 ∧ p2) ∧ (True ∨ (p1 ∨ True))) → p1) ∨ (False → p4))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
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
theorem thm_5_vars_192734869005377861577451143530 : ((((p3 → p5) ∧ (((True → p4) ∨ True) ∧ p1)) → p5) → (((((True ∨ (p1 → False)) ∨ p1) → p3) → p4) ∨ ((p2 ∨ False) → (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173155273015291235211449296705 : ((p3 ∨ ((False → p1) → ((p5 → (((p5 → (p4 ∨ False)) → False) ∧ True)) ∨ p5))) ∨ ((p2 ∧ (((p2 ∨ p1) ∨ (p5 → True)) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300110602772576596220657107199 : (False ∨ (((False ∨ ((((p2 ∨ p5) ∧ p3) ∨ p1) ∨ p5)) ∧ (p5 ∧ (((p5 → p4) ∧ p5) ∧ ((p4 → (p2 ∧ True)) ∨ False)))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172382326540025662732516480391 : ((((((p3 ∧ p4) → False) → False) ∨ p1) → ((p1 ∧ (p3 ∧ (p2 ∧ False))) ∨ p2)) ∨ ((p5 → False) → ((p4 ∨ (p1 ∧ True)) → (p4 → True)))) := by
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
theorem thm_5_vars_161605256531464620967002701896 : ((False ∨ ((((p3 ∨ False) → (((p4 ∧ p3) → p4) ∧ p1)) → (True ∧ (False → (p2 ∧ False)))) ∨ p4)) → (((p3 ∧ p4) ∨ (p1 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_165221669656370386377854260777 : ((((((p1 → p3) ∨ (p5 → False)) → p1) → (p5 → ((p1 → True) → p2))) ∨ (p2 → p1)) ∨ ((p4 ∧ (((p3 ∨ p1) → p1) ∧ p2)) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119124116600550801250377898655 : ((p1 → (p3 ∧ ((p3 ∧ (((((p3 ∧ p2) → p4) → ((p5 → p3) ∨ p3)) ∧ ((p5 → (p5 → False)) → p1)) ∨ p1)) ∧ p1))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112179963942692734742302697171 : (((p4 ∧ ((p2 → p1) ∧ (((p1 → (((p3 ∧ (((p2 ∨ True) ∧ False) → True)) ∨ (p2 ∧ p2)) ∧ True)) ∨ p5) → False))) ∨ True) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608556876474615271198133799038 : ((((((p1 ∨ (p5 ∧ (p1 ∨ ((p2 ∧ (p2 ∧ ((p5 ∨ (p5 → p1)) → (True ∧ False)))) → ((False ∨ p4) ∧ p4))))) → p1) ∨ p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149663499715711326527599733578 : ((p4 ∧ (False ∨ ((((p2 ∧ (p3 ∨ ((((p1 ∨ p5) ∨ (p5 ∨ p3)) ∧ p5) ∧ p2))) ∨ False) ∧ True) ∧ p3))) ∨ (((p4 → p3) ∧ False) → p2)) := by
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
theorem thm_5_vars_639124594119951647213505681556 : ((((((True ∨ p2) ∨ (True ∨ p1)) ∨ ((True ∨ ((p5 ∨ ((((p2 → p5) → p5) ∧ False) ∨ (p2 ∨ p2))) → p4)) ∧ (True ∨ p3))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205949309570241817266496515194 : ((False ∧ (True ∨ (p5 ∨ (True ∧ p4)))) ∨ ((p5 ∨ p5) → (((((p5 ∨ p3) ∧ (((p2 ∨ p1) ∧ (p4 → p2)) → p3)) ∧ p4) ∨ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113816991678211460779603736066 : (((p2 ∧ (p4 → (p4 → (p2 → ((p5 ∧ (((False → (p3 ∧ p1)) → p4) ∧ p4)) → ((True ∨ p5) → True)))))) → (p3 ∧ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171454483415336381958254512393 : (((p4 ∧ (((p4 ∨ (p5 ∨ p2)) → (p5 ∧ (p1 ∧ (True ∧ p5)))) ∧ True)) ∧ True) ∨ (((((p3 → p1) ∧ (p4 ∨ p3)) ∧ p3) ∧ p2) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599093227657063459774931432767 : (((((True → p5) ∧ ((p4 ∧ (p5 ∨ p1)) ∨ (p3 → (((((False ∨ p2) ∨ (False ∧ (p3 ∧ p5))) ∧ (p1 ∧ p4)) ∧ p1) ∧ p2)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54930399675640477898042506548 : ((((p5 ∧ (p5 ∧ (p5 → p1))) → False) ∧ ((p1 → False) ∨ ((p4 → p3) ∧ ((((p2 ∧ True) → p5) → (p5 ∨ (p2 → p1))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43393612803491335330176698978 : ((((((p5 ∨ (True → ((p5 → ((True ∧ (p1 ∨ False)) ∨ True)) ∨ p3))) ∧ p5) ∧ (p2 ∧ ((p2 → (True ∧ p3)) ∨ p5))) ∨ p3) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159578057214980863808472867235 : (((True → (p1 ∨ ((p1 ∨ (((p1 → p5) ∨ ((p2 → p3) ∧ (False ∨ p2))) ∨ p5)) → False))) ∧ p5) → (p2 → (p2 → ((p3 → False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (((p1 → p5) ∨ ((p2 → p3) ∧ (False ∨ p2))) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355132108969407663149309736968 : (p5 → (((False ∨ ((p3 ∧ p2) ∨ ((((p2 ∨ (((p1 ∨ p5) ∨ (p5 ∨ (p1 ∨ p3))) ∨ p5)) ∨ p3) ∨ p4) ∨ p4))) → (p2 ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ ((p3 ∧ p2) ∨ ((((p2 ∨ (((p1 ∨ p5) ∨ (p5 ∨ (p1 ∨ p3))) ∨ p5)) ∨ p3) ∨ p4) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172280577322081083454598784911 : (((p1 ∧ (p4 → (p3 ∨ (p1 → (p1 → p1))))) ∨ (p5 ∧ (p2 ∧ (p3 ∨ p4)))) ∨ ((p5 → ((p3 → (p2 ∧ True)) ∧ True)) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679034979264399258886187668054 : ((((False ∨ ((((((p4 → (p4 ∨ (p2 ∨ False))) → (p1 ∨ p2)) ∧ True) ∨ (p3 ∨ p5)) ∧ p2) → p5)) ∨ (False → ((p2 ∧ p1) → p3))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354631851872031460517332788357 : (p5 → (((p4 ∨ (((p1 → (True ∧ (p5 → p2))) ∨ (False ∧ (p1 ∧ ((p1 ∧ ((p3 ∨ True) → p1)) ∧ p5)))) ∨ (p4 → False))) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40451830648156878613408325433 : (((((p1 ∨ ((p3 ∨ p3) ∨ (p3 → p3))) → ((p4 ∨ p3) ∧ (((p3 ∧ p5) ∧ (p3 ∨ (p2 ∨ (p3 → p2)))) → p4))) ∨ p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181509045075319503671348217624 : ((p5 ∨ (p5 ∧ (((True → p2) ∧ ((False ∧ p1) → True)) ∧ (p4 ∧ p4)))) → ((p4 ∨ (p3 ∧ (False ∨ p2))) ∨ ((p2 → p4) ∨ (p2 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117017459361972900963544091375 : (((p1 ∨ p3) → (((p1 ∧ p2) → (((True ∨ False) ∧ (p3 ∨ (p2 ∧ ((True → False) ∧ p1)))) ∧ ((p4 ∧ True) ∨ True))) ∧ p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136118947047372834429635346464 : (((p5 ∧ ((True ∧ p5) → (False ∨ (p3 ∧ p4)))) ∨ (p4 ∧ (True ∧ ((p4 → (p4 ∧ True)) ∧ (p2 → (p4 ∧ p5)))))) ∨ ((False ∧ p1) → False)) := by
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
theorem thm_5_vars_344831688149869680959474249645 : (p2 → (p5 → ((((p2 ∨ (p1 ∨ True)) ∧ (p3 ∧ (((False ∨ (p1 ∧ (p5 ∧ (False ∧ ((p2 ∧ p4) ∧ p1))))) ∧ p5) ∨ p2))) ∧ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927636956894728407867097640642 : ((((((False → False) ∨ (((True ∨ p3) ∧ False) ∨ False)) → False) ∧ ((((p5 ∨ p2) ∧ (((p2 ∧ p2) ∧ p5) → (p1 ∧ p5))) → p2) ∨ True)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False → False) ∨ (((True ∨ p3) ∧ False) ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((False → False) ∨ (((True ∨ p3) ∧ False) ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52597761048670879974071736527 : ((((((p2 ∨ p5) → (False ∧ False)) ∧ p1) ∨ (p4 ∧ ((p3 ∧ p2) ∨ p4))) ∨ ((((p5 ∧ p5) ∨ p1) → (p1 ∧ p3)) ∧ (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135609981783418599314506075350 : (((p2 ∧ ((p5 ∧ ((p1 ∨ (p5 ∧ True)) ∧ (((p5 ∨ p5) ∧ p2) ∨ p5))) ∧ p5)) ∨ (p5 ∧ ((p3 ∧ p1) ∨ p1))) ∨ ((p2 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315769777479151066908494776171 : (p3 ∨ ((p1 ∧ p3) → ((p1 → p1) ∧ ((p3 ∨ (p5 → False)) ∧ (p5 ∨ (((p3 ∨ p3) ∧ (p1 ∨ (p1 → False))) → (p2 ∨ (False ∨ p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217815118901836950688560797115 : (((p2 ∨ (False → p4)) → p5) → (((True ∨ (p3 ∨ (p3 ∨ p3))) → (p2 ∨ (p5 ∧ (p5 ∨ p3)))) ∨ (True → (((p4 ∧ p4) → p3) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196765958839835697276708126184 : (((((p5 ∧ True) ∨ p2) → (False ∨ p1)) ∧ p3) ∨ ((p5 ∨ True) ∨ ((True ∧ p2) ∨ ((p2 ∨ (((p4 ∨ p1) → p1) ∧ (True ∧ p1))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245370806126163557009138849745 : ((p2 ∧ p3) ∨ (((p5 ∧ False) ∧ (p3 ∧ p2)) ∨ (p5 → (((True ∧ ((False → p1) → p4)) → ((p3 ∧ p4) → (p4 → True))) ∨ (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_138446983589088193026994575589 : ((p5 → ((p2 → False) ∧ ((((p1 → p4) → ((True ∧ (p1 ∨ (p4 ∧ p3))) ∧ (True ∨ p1))) ∧ (p4 → p3)) → p1))) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64912632984189737697606310998 : ((p2 ∨ (((True ∨ p4) ∧ (((p5 ∧ p1) ∨ (False ∨ ((p2 ∨ (p2 ∧ True)) ∧ (p2 ∨ p1)))) → p3)) → ((p4 → (True ∧ False)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323805063184005673554643040256 : (p5 ∨ ((p2 ∧ ((p2 → ((p3 ∨ p5) ∧ (p5 → (True → (p5 → p3))))) ∨ ((p5 ∧ p3) → p4))) ∨ (((False → p1) ∨ (True ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179644576305444363311273659432 : ((p5 → (((p1 ∨ ((False → False) ∧ p4)) → ((p1 ∨ False) ∨ False)) ∧ p4)) ∨ (False → ((p4 → p4) ∧ ((p5 → p4) ∨ (p4 → (p1 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_105437960775892436796775398574 : ((((((((p4 ∧ True) ∨ ((p4 → False) ∨ (p3 → p4))) → p5) → (p3 ∧ p5)) ∧ True) ∨ p3) ∨ (((p4 ∨ False) → p1) ∨ True)) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788875630560624485531626102087 : (((p5 ∨ (((((p2 → (p2 ∨ p3)) ∧ p5) → p2) ∧ ((((p2 ∧ (p3 ∧ (p1 → (p1 ∨ p2)))) ∧ True) ∨ False) ∧ p1)) ∧ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49474533548491580929423434264 : (((((((p1 ∧ (p2 → False)) → ((p5 ∧ (p1 ∧ (((p1 → True) ∨ False) → True))) → p1)) ∧ p2) → p1) → p1) → ((p2 → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84096371713293197215115757276 : ((((p2 ∨ ((p3 ∨ True) ∨ True)) → ((p5 → ((True → p3) ∧ True)) ∧ (False ∧ False))) ∧ ((((p4 ∨ p3) ∨ (False ∧ p1)) → p4) ∧ True)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ ((p3 ∨ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183906321752633192866858462865 : ((((True ∨ p3) → ((p4 ∨ (False ∨ (p2 ∨ p4))) ∧ p2)) ∧ p4) ∨ (((True → ((p5 ∧ p4) ∧ p2)) ∨ False) → (False → ((p2 ∨ p3) ∧ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602680696747220948017822078054 : ((((False ∨ ((p5 ∨ (((p3 → (p1 ∧ False)) ∧ p2) → p2)) → ((p1 ∨ ((False ∧ True) → p4)) ∧ (((True → p2) ∨ p4) → p1)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44542042817836705032308022893 : ((((False ∧ (((p5 ∨ p4) ∨ (True ∧ (p5 → p1))) → p3)) → ((p1 ∨ (True ∨ p1)) ∧ (p3 ∨ ((p3 ∨ (p4 → p4)) → True)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357273387107085143219903262189 : (p5 → ((p4 ∧ False) ∨ ((p2 → ((((p5 ∨ (True ∧ p1)) → p5) → (((p1 ∧ p4) ∨ p4) ∨ True)) ∨ p4)) ∨ ((False → (False ∨ p4)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18118890623912794241208295270 : (((p2 → ((p3 ∧ (p2 ∨ (p2 ∨ (p5 ∨ p2)))) ∧ (((p4 ∨ (False ∧ p1)) ∧ (p4 ∨ p1)) ∧ False))) ∨ (False → ((p4 ∨ p5) → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164842008658106382258809469235 : (((p3 ∧ ((p2 ∧ ((p1 ∨ (((False → p5) → p3) → False)) ∧ p5)) ∨ (False → p1))) ∨ p5) ∨ (p1 → ((p5 → p2) ∨ ((p2 ∨ p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783343433836552343473883373342 : (((p3 ∨ (((p5 ∧ ((((((p5 → (True → True)) → p5) ∧ p5) ∨ p2) ∧ p3) ∨ p3)) ∨ p4) ∧ ((p1 ∨ p2) ∨ (False ∨ (p3 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350268914081752725618875278548 : (p4 → ((p3 ∧ (p1 ∨ (((p5 ∨ (p4 → p4)) ∨ p1) ∧ (((p2 ∨ (True ∧ (False ∨ (False → (p3 ∨ False))))) ∨ p3) ∨ (p5 ∧ p2))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650975647581374865140079617887 : (((((True → (p1 → (p5 → (p2 → p4)))) ∨ ((p2 ∨ True) ∧ ((p1 ∨ ((p3 → p3) ∧ (p2 ∨ p1))) ∨ (p3 ∨ False)))) ∧ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183909563187400897440466041710 : ((((p1 → p4) → ((((True ∧ p1) ∨ False) → True) → p5)) ∧ True) ∨ (True ∨ ((((False ∨ (p2 ∧ (p3 ∧ p3))) ∧ p1) → False) → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620324778692074073671984076545 : (((((p1 ∨ p2) ∨ (p1 ∨ ((p4 ∧ (((p1 ∧ True) ∨ ((((p3 ∨ (p2 ∧ p2)) ∨ p3) → p1) ∧ True)) ∨ (True → p2))) ∨ True))) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51617378189112406313305881127 : (((((((((p4 ∨ True) ∧ p1) ∨ p2) ∨ p4) ∨ True) → ((True ∧ p2) ∧ p5)) ∧ True) ∧ ((p3 → p3) → ((p2 → (p1 ∧ p3)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651857133382981713580771653723 : (((((p1 ∨ p1) → ((p1 → (((p5 ∧ ((p1 ∧ p1) ∧ (p3 → p4))) ∧ (p2 ∧ p1)) → p3)) → (p4 → (False ∨ p2)))) ∧ (p5 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322250341687855505479946797253 : (p5 ∨ ((((False ∨ (p3 ∧ ((((((((p2 ∧ p1) ∨ p1) ∧ True) ∧ p5) ∧ p1) ∨ True) ∧ False) → False))) ∧ ((p5 ∨ True) → p1)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710751193232572932849239983663 : ((((((p2 → False) → False) → (p4 ∨ p5)) ∧ (p1 ∨ ((((p3 ∧ ((p2 ∨ (True → True)) ∨ (p5 ∨ p5))) ∨ p3) ∨ (p3 → p2)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626819408391272165331547716697 : ((((p5 → ((p3 ∧ (((p5 ∨ p5) → p5) ∧ p3)) ∧ (((p3 ∧ p2) → ((p5 ∧ p5) → ((False ∨ False) ∧ p2))) ∧ (p2 ∨ p1)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229410249729930781244395172405 : ((p1 → (p4 ∨ p2)) ∨ ((p5 ∧ p5) ∨ (((p3 ∨ ((False → (True ∨ p4)) → (True → (p3 ∨ False)))) ∨ ((p2 ∧ True) ∧ p3)) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_134006823883165870689619549224 : ((((p3 ∧ (p1 ∧ ((p1 ∨ p5) → ((False ∧ p1) ∧ ((((p2 ∨ (p2 ∧ p1)) → p3) ∨ p4) ∧ p1))))) ∧ p4) ∨ p4) ∨ ((p2 ∧ False) → p3)) := by
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
theorem thm_5_vars_201782673552754709132806793411 : (((((p4 → p2) ∨ p5) → p3) ∨ True) ∧ ((False ∧ (True ∧ p5)) ∨ (((p2 ∧ (p1 → ((p3 ∨ p5) ∧ p5))) ∧ (p5 → p4)) ∨ (True ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355529110635512292661090358607 : (p5 → (((((((False ∧ True) ∨ ((p3 ∧ (p2 ∧ True)) ∨ p3)) → ((p4 ∧ (p2 ∨ p3)) ∨ p3)) ∧ p5) ∧ (p2 ∨ p5)) ∧ p2) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149694747404117930631221093373 : ((p5 ∧ ((False ∧ (p1 → (((p1 → False) ∧ p2) → p5))) ∧ (p5 → ((True → p4) → (p3 ∧ (p5 ∧ p3)))))) ∨ (p3 ∨ (p5 → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624350050091637564305385509903 : ((((p3 ∨ (((p2 → p1) → (p2 ∨ p4)) ∨ ((((((p2 ∧ p3) → (p2 ∨ p4)) ∧ ((p5 ∨ p5) ∧ p4)) ∧ p1) → False) → True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_158344549919432716584485555346 : (((p3 ∧ p5) ∧ (p3 → (p3 → (((p3 → ((p1 ∧ (True ∨ p4)) ∨ (p4 ∧ p3))) ∧ p5) ∨ p1)))) ∨ ((True → (p4 ∧ (p5 → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114017077713636857025062315885 : (((((((p1 ∧ p2) ∨ p2) → ((p5 ∧ p2) → ((p2 ∨ (p2 ∨ True)) ∧ False))) ∧ (p5 ∧ p3)) ∨ p3) ∨ (False → (p3 ∧ p3))) ∨ (p2 → p1)) := by
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
theorem thm_5_vars_166225366986812864872733453610 : ((p2 ∧ ((((p5 → (p2 ∧ False)) ∨ p4) ∧ (False → p2)) ∧ (True ∧ ((p2 ∨ True) ∨ p2)))) ∨ (((p2 ∨ False) ∧ p4) → (False → (p2 → True)))) := by
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
theorem thm_5_vars_350266258771526939423158253362 : (p4 → ((p3 ∧ (((True ∧ ((p3 ∨ ((False → (p2 → (p3 ∧ p2))) → ((p4 → False) ∨ p5))) ∧ p1)) ∧ p4) ∨ ((False ∨ p2) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864262625478217455443135730807 : (((((((p4 ∧ p5) → p1) ∨ (p1 → ((p5 ∨ p4) ∨ p3))) → ((p4 → p3) → (True → (((False ∨ p4) ∨ (True ∨ p5)) ∨ p4)))) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ p5) → p1) ∨ (p1 → ((p5 ∨ p4) ∨ p3))) → ((p4 → p3) → (True → (((False ∨ p4) ∨ (True ∨ p5)) ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693153929213813084038407844626 : ((((p5 ∧ ((((p5 ∨ False) ∧ False) ∧ False) ∧ (p1 ∨ ((p2 ∧ p1) ∨ False)))) ∧ ((False ∧ p5) ∧ ((True → True) → (False ∧ (p2 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168640154866477967432027206503 : ((p4 ∧ ((p4 → ((p2 ∧ (p5 → (False ∧ (p3 ∧ p2)))) → ((p2 ∧ False) ∧ False))) → p4)) → ((p5 ∨ (p2 ∨ (p1 ∧ (p1 ∧ p3)))) ∨ p4)) := by
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
theorem thm_5_vars_694142695338172240654063360028 : (((((p4 ∨ ((p3 ∨ p3) ∧ (p2 ∨ p2))) ∧ (((p1 → p3) ∧ p3) ∨ False)) ∨ ((p5 ∧ (p2 ∧ p2)) ∧ (p2 → ((p1 ∧ p5) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55448776611979725337918810332 : (((((p3 ∨ p2) → (True ∨ p5)) → p1) → (((p5 → (p2 ∨ p5)) ∨ p2) → (((p2 ∨ ((False ∧ (p1 ∨ p3)) ∧ p5)) ∧ False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355839381117521254039313670846 : (p5 → (((p3 ∧ (p3 → ((p2 ∨ (p1 ∨ (p4 → (p1 → p2)))) ∨ (p1 → (p3 ∧ ((p3 → p1) ∨ p2)))))) ∨ p3) ∨ (p4 ∨ (p5 ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593141772310601284991936357152 : (((((((((p1 ∧ (False → p1)) ∧ (p3 ∧ False)) → p2) ∨ p4) → ((True → ((p1 ∧ p3) ∨ p5)) ∨ True)) ∨ (True → (p5 ∧ p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50194641222367823591397301356 : ((((False ∨ (p2 ∨ ((p2 → ((p3 ∨ p2) → (p5 ∨ (p3 ∧ ((p1 ∧ p1) ∨ True))))) ∧ p2))) ∧ p2) ∨ (True → ((p5 ∨ p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308504290013122570370277228080 : (p2 ∨ ((((False ∧ p4) ∧ (p3 ∨ ((False ∨ True) ∨ (p3 ∧ (True → ((p5 ∨ p5) → (p2 ∨ True))))))) ∨ (False ∧ (p1 ∨ (True → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258767237434627184203070763694 : ((True → False) → ((p4 ∨ (False ∨ (((p5 ∧ True) ∧ ((p4 → (False → ((p5 ∧ (False → p3)) ∨ (p3 → (p1 ∨ True))))) ∨ True)) → p3))) ∨ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238025488433226753926318412866 : ((True ∨ p1) ∧ (((p4 ∧ p5) ∨ True) → (((((p3 ∧ (True → False)) ∧ (p4 → p1)) ∧ p5) ∨ ((p1 ∧ p5) ∧ ((p5 ∧ p3) ∨ p5))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_326880354927946148681726436705 : (True → ((((((p2 ∨ p1) ∧ False) ∨ (False ∨ p2)) ∨ ((p5 → (p1 ∧ (p5 ∨ ((p2 → p2) ∨ True)))) → ((p3 → p1) ∧ True))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309366340796459264953706621797 : (p2 ∨ ((((p5 ∨ p5) ∨ False) ∧ (p1 → (((p3 ∧ p1) ∧ p1) → (p5 ∧ (p4 ∧ (((p4 → p3) ∧ p3) → (p3 ∧ p3))))))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339503700108056134104631991002 : (p1 → (False ∨ ((((p1 → False) ∧ p2) → (False ∨ ((p3 ∨ p3) ∧ (p5 ∧ True)))) ∨ ((p1 ∨ (False → (p5 ∨ (p2 ∨ (p5 ∧ p2))))) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798210094081680541193666531644 : (((p1 → ((p2 ∧ ((p1 → ((True ∨ (p3 → (((True → True) ∧ p2) ∧ (p5 ∨ False)))) ∨ True)) ∧ p1)) → (p3 ∧ ((p5 ∧ p3) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260523707167122406758455548739 : ((p3 → p1) → (((((p2 ∧ True) ∨ p4) ∨ (((((p3 ∨ (False ∨ (False ∨ ((p5 ∧ p1) → p1)))) → p3) ∧ p5) ∧ p2) → p1)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



