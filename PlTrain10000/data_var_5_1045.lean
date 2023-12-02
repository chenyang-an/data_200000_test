variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56872308505638981938188809490 : (((p1 ∧ (p5 ∨ p5)) ∧ (((False ∨ p1) ∧ (((p5 ∧ True) ∧ p5) → True)) ∧ (p5 ∨ ((p4 ∨ (p2 ∧ (p3 → p2))) → (p4 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314413829766372558136328036735 : (p3 ∨ ((((p5 ∧ (((p1 ∧ False) ∨ p3) → p1)) ∨ (((p5 → p1) → (p3 ∧ True)) ∨ p2)) ∧ (p5 → p5)) ∨ ((True → p5) → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53862014369391324992463366590 : (((((p5 → False) → True) → ((p5 ∨ p4) ∨ (False ∨ p1))) ∨ (False ∨ ((p1 → p2) ∨ ((p1 ∨ ((p3 ∧ p1) ∨ p4)) → (False → True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207097227046814401718074037789 : (((False ∨ ((p5 ∧ p5) → p5)) ∧ p3) → (((((((True → True) ∨ True) ∧ p2) ∧ ((p5 ∨ True) ∨ False)) → (p2 → p4)) ∨ (False → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46837201976554417409478179030 : ((((((p2 → (p4 ∧ (p2 ∧ ((p3 ∧ p1) ∨ p1)))) → p3) ∨ (((((p3 → False) ∧ True) ∧ p3) ∨ False) ∨ False)) ∧ p4) ∨ (p2 → p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56536277775016553027721371475 : (((False ∨ (p2 → (p1 → p2))) → ((p4 ∨ (p5 ∨ (((True ∧ p3) → False) ∨ ((p2 ∧ p5) ∧ (p5 ∧ p4))))) ∨ (True ∨ (p5 → p2)))) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113099681116130231738664544987 : (((True → ((((((False ∧ p3) → p4) ∧ (p2 → p3)) ∨ (((p2 ∨ (p2 → p1)) → (p5 → p4)) ∧ p2)) ∨ p2) ∨ p3)) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248343514155730007707430440416 : ((p2 ∨ p3) ∨ ((False ∧ (((p4 ∨ p3) ∨ (p4 ∨ p5)) ∧ p2)) ∨ (((True ∧ (((True ∧ p2) ∧ p1) ∧ p1)) ∧ p3) → (False ∨ (p5 → True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697895413502751296630393477 : ((((p2 ∧ (True ∧ p5)) ∨ (True ∧ (True → (True ∧ (False ∨ False))))) → (((False ∨ p3) ∧ (True ∧ (p3 ∨ p5))) ∨ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256831904510650562374049782091 : ((p1 ∨ p3) → (((((p4 ∨ (p2 ∧ True)) ∧ ((((True → (p5 → False)) → True) ∨ p4) → p1)) ∨ ((p2 → False) ∨ p3)) ∨ p5) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36984640974708979691360616563 : ((p5 → (p2 ∨ (((p4 → (True → (p2 → ((((((p5 → (True → p5)) ∧ p1) → False) → False) ∧ (p5 ∧ p3)) ∨ p5)))) ∧ p2) ∨ True))) ∧ True) := by
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
theorem thm_5_vars_354649658343295031711703318700 : (p5 → ((((((p3 → (p3 → (p1 ∨ p5))) → ((((p2 ∨ p4) ∧ p1) → p1) ∨ (p1 ∨ (p2 ∨ p1)))) ∨ p4) → (p5 ∨ p2)) → p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725122644968823950446595452210 : ((((p1 → (p5 ∧ p2)) ∧ (p5 ∨ ((p3 ∧ (((((p1 ∨ p3) ∨ ((p2 ∧ ((p4 ∨ True) ∧ p4)) ∧ p4)) → p4) → True) → p4)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171898221172073120604233716115 : (((p4 ∨ (p2 → (p3 ∧ (True ∧ ((False → ((p4 → p1) ∧ False)) ∨ p4))))) → p1) ∨ (((p4 ∨ False) → False) ∨ (p4 → ((p5 ∨ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37633645994171511526126862138 : ((((((((p2 ∧ (True → (p2 ∨ (True ∨ p1)))) → (p1 ∧ p4)) ∨ (p5 ∧ False)) ∨ (p3 ∧ (p5 ∧ (p3 ∨ False)))) ∨ p4) → p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310048837116311151079738882769 : (p2 ∨ ((((((False → p2) ∧ p2) → (True ∨ True)) → (p3 ∧ (p2 → (p2 ∧ p1)))) ∧ p4) → (((p3 → p5) → False) ∨ ((p2 → True) ∧ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116552111261087263005421774541 : (((p1 ∨ p1) ∧ ((True ∨ (p5 → ((p4 ∧ (p4 → p1)) ∧ p3))) ∧ ((p2 ∧ ((True ∨ p1) ∧ (False ∧ False))) ∨ (p1 ∨ True)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50428408891283588620543892430 : (((p4 ∧ (p3 ∨ ((((p3 ∨ (p5 ∧ p1)) ∧ (False → p5)) → (((p5 ∧ p5) ∧ p5) ∨ p3)) ∨ p4))) ∨ (((p4 ∨ True) ∧ p1) → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175363316089476910852403281532 : ((p5 ∨ (p4 ∨ (p3 ∨ (p3 ∨ ((False ∨ (p1 → p1)) ∨ ((p5 ∨ True) → p1)))))) → ((p2 ∨ (p4 → (True → p4))) ∨ (p1 ∧ (p5 ∧ False)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h21
              -- Implications on the right can always be decomposed.
              intro h22
              -- One of the premise coincides with the conclusion.
              exact h21
          case inr h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- One of the premise coincides with the conclusion.
            exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356398832521552021522922745962 : (p5 → ((p2 → (p4 ∧ (((p5 ∧ False) ∧ ((p5 ∨ p3) ∧ True)) ∨ (p1 ∨ p5)))) → (((p1 → (p2 ∨ p3)) ∧ p1) ∨ ((p2 ∨ p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_450892333472484071042076682032 : ((((((True ∨ (((p5 ∨ True) ∨ p1) ∧ ((False ∨ (True → (p2 ∨ False))) → (p4 → p3)))) → p2) ∨ p5) ∨ (((p2 ∨ p3) ∨ p5) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_40297937680038268197256196505 : ((((((((p5 ∧ (True ∨ (p5 ∨ p4))) ∨ (p1 → ((((p4 → p2) ∧ True) → p4) ∨ False))) ∧ (p4 ∨ p4)) ∧ p3) ∧ p2) ∨ True) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613734812424760214223421146488 : ((((((p1 ∨ True) → (p5 ∨ (((False ∧ p4) ∨ ((True ∧ p1) → (p4 ∧ True))) → (False ∧ (p5 → p5))))) ∧ (p4 ∧ (p3 ∧ p5))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189136917740691339221130064324 : (((p3 ∨ True) ∧ (p3 ∨ (p2 ∨ (p1 ∨ (True → True))))) ∧ (False ∨ (((p3 ∧ ((p3 → p4) ∨ (p4 → p5))) ∨ (p3 ∨ (p1 ∨ True))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_340337028081367945437396487064 : (p2 → (((p3 ∨ ((((((p1 ∨ p4) → True) ∧ ((p2 ∨ False) → p3)) ∧ (p3 → p3)) → (p1 ∨ ((p4 ∧ p3) ∨ p5))) → p3)) ∨ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47113868653666715692597405047 : (((((((p4 ∨ p5) ∨ (p3 ∧ p4)) ∧ (p5 ∧ ((p4 ∨ p2) → p2))) ∧ (p4 ∨ (p4 ∨ True))) ∨ (p4 ∨ (p3 → True))) ∨ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351416772106601111070027985698 : (p4 → (((True ∨ p4) → (((((True → p5) → True) → p4) → True) → (((p2 → (p1 ∧ p4)) ∨ p2) ∨ True))) ∨ (((p1 → p3) → p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_304757213835868058493859250548 : (p1 ∨ (((p4 → False) → (((p4 ∨ ((False ∨ p1) → ((p1 → False) ∨ p3))) ∧ (((p2 → (p5 ∧ p3)) ∨ p5) → p5)) → p4)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321111190477393294446428960614 : (p4 ∨ (p2 ∨ (((((p5 → p1) ∨ (p2 ∧ (p5 → (True → (p5 ∧ ((True ∧ p5) ∧ p1)))))) → p5) ∨ (p2 → (p1 → (p4 ∨ True)))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219496951227009583171502528643 : ((p5 ∨ ((True ∨ p1) ∨ p4)) → (p4 → (p5 → ((((True ∨ p3) ∨ (p2 → p5)) ∨ p2) → ((p4 ∨ (True ∧ (p4 ∧ p2))) ∧ (p3 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h12 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h2
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h19 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h2
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h26 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h41 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h42 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
          case inr h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h45 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h48 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h44
            case inr h49 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h44
          case inr h50 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h44
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h52 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h52
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h56 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h57 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h58 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h59 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h59
    case inr h60 =>
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h64 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209333472347340730680823716722 : ((False → ((False → (p2 ∨ p2)) → p4)) → ((((False → False) → p3) ∧ p4) ∨ (p5 → ((((p4 ∨ (p5 ∨ p4)) → (p4 ∧ p5)) → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657067087629736494270142649346 : (((((True ∨ (p3 ∧ False)) ∧ (True ∧ (((p4 → p4) ∨ (p2 → ((((True → (p5 ∧ p5)) → p3) ∨ p3) ∨ p2))) → p3))) ∨ (False ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56206157762507387875181374629 : (((False ∨ ((p4 ∨ False) → False)) ∨ ((((((p5 ∧ p3) ∧ (p5 ∨ p5)) ∧ p3) → p3) ∧ (True → (p2 ∧ (False ∨ (p5 ∧ p2))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172650830368604885033597564978 : (((p3 ∨ p4) ∧ (((False ∧ p1) ∨ p2) ∧ ((p2 ∨ p3) ∨ (p4 → (p4 ∨ p5))))) ∨ ((p4 ∧ False) → (p5 ∨ (((p3 → p5) ∨ True) ∨ False)))) := by
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
theorem thm_5_vars_215163277036819170404610126388 : ((True ∧ ((p2 ∧ True) ∨ False)) ∨ (((p2 ∧ (((True ∧ p4) ∨ (p4 ∨ (True → (p3 → p1)))) ∧ p2)) ∧ p2) ∨ (p4 ∨ ((p5 ∧ False) → p1)))) := by
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
theorem thm_5_vars_689220880747547438219704573883 : ((((((p5 ∧ p3) ∨ (p1 ∨ (((False ∨ ((True → p2) ∧ False)) ∧ True) → p4))) → p5) ∨ (True ∧ ((p1 → ((False → p2) ∧ p5)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779919311298560729792850870747 : (((p2 ∨ (((((p2 ∧ p1) ∨ p5) → ((p3 ∨ ((((p1 → (p5 ∧ p1)) → p2) ∨ (p2 ∧ p5)) → p4)) → False)) ∨ p4) ∧ (p5 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148888116530539123587209030474 : ((((p1 ∧ p1) ∨ (False ∧ True)) ∨ ((p5 ∨ (p4 ∨ ((p3 ∧ p3) → (p3 → (p5 ∨ True))))) → (True ∧ p1))) ∨ (p2 ∨ (True ∨ (False ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67843210461427310620967902873 : ((p2 → (((p3 → p4) ∧ ((True ∧ p4) → (((((True → (True → p2)) ∧ p2) ∧ (p4 → (True → p1))) ∨ True) → p5))) ∨ (p2 ∧ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62270864194100076581749379172 : ((p3 ∧ ((((p2 ∨ p5) ∨ ((True ∧ (p3 ∧ p1)) ∨ ((True ∧ p5) → (p2 → (True ∧ ((p1 ∨ p5) ∧ p5)))))) ∧ (p1 → p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179900120441895069945321271599 : (((((True → (((True ∧ p5) → p2) ∨ (False → False))) ∧ p4) ∨ True) ∨ p3) → ((((True → p3) ∧ (True ∨ (p2 ∨ (p1 ∧ p4)))) ∧ p2) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h25 := h5 h24
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h28 := h5 h27
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h37 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h38 := h5 h37
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h40 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h41 := h5 h40
          -- One of the premise coincides with the conclusion.
          exact h41
      case inr h42 =>
        -- One of the premise coincides with the conclusion.
        exact h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259044145605793936372578482025 : ((True → p4) → (True ∧ (p2 → (((((p3 ∧ (((p3 ∧ ((False ∨ True) ∨ (p4 ∨ p3))) ∨ False) ∧ (p2 ∨ True))) ∧ p2) ∨ p4) → False) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ (((p3 ∧ ((False ∨ True) ∨ (p4 ∨ p3))) ∨ False) ∧ (p2 ∨ True))) ∧ p2) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44516845132750751773791620758 : ((((((True ∨ p4) ∧ p5) ∧ (False ∧ (p2 → (p1 → p1)))) ∨ (((True ∨ p2) → (False ∨ (p5 → (p5 ∨ (True ∧ p3))))) ∨ False)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256110019352773809046849970851 : ((True ∨ p5) → ((p4 → (((True ∨ False) ∨ False) → (p2 ∨ ((p1 ∨ p5) ∧ (((p2 ∨ p1) → p5) → p4))))) ∨ ((True → True) ∨ (False ∨ p3)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352768915219124510121831888833 : (p4 → ((p4 ∧ p1) → ((((((p5 ∧ ((True → (False ∧ p3)) → (p2 ∧ p1))) → (p5 → False)) ∧ False) ∧ False) ∨ (p4 → (p1 ∧ True))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653955619281970065099376331911 : (((((True ∧ (p2 ∨ ((((((True ∨ p2) → p2) ∨ p2) ∧ p3) ∧ False) ∧ ((((p2 ∧ p5) ∧ p4) ∧ p3) → p1)))) ∧ p4) ∨ (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317344974396197393696303804866 : (p4 ∨ (((p3 ∨ (p5 → ((True → (True ∧ (p3 → p3))) ∨ (p4 ∨ (p3 ∧ False))))) ∧ (p3 ∨ (p2 ∨ ((p4 ∧ (p5 ∧ p2)) ∨ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
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
theorem thm_5_vars_118891251582978518057315435835 : ((True → (p5 ∧ ((False ∨ ((((p4 ∨ p2) ∧ (p2 ∨ (p5 ∨ False))) ∧ (True → p1)) → (p4 ∧ ((False → p5) ∨ p1)))) ∨ p2))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69142201409367148459231747692 : ((p5 → (((((False ∨ (p2 ∧ True)) ∧ (((p5 → p4) → True) ∨ p3)) ∧ False) ∨ ((p1 ∨ (p1 → p4)) ∨ p1)) ∨ (p3 ∨ (True → p5)))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168146842343275412572390907090 : (((p4 → (True ∨ (p5 ∨ True))) → (False ∨ (p2 ∧ (True → (((False → p1) → p2) → p3))))) → ((p2 ∧ ((p3 → True) ∧ (p4 → p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (True ∨ (p5 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252283683820940120330188518199 : ((p4 → p5) ∨ (((p1 ∨ (p1 → ((p2 ∨ ((p1 ∨ p1) ∨ p5)) ∧ (p2 ∧ p2)))) ∨ ((True → p1) → p2)) ∨ (p5 → ((p3 → True) ∨ True)))) := by
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
theorem thm_5_vars_199063665199489607939691838893 : ((((((p2 ∨ False) → p1) ∧ p3) → p2) ∧ p4) → ((True → p3) ∨ ((p1 ∨ (p5 ∧ False)) ∨ ((False ∧ p5) → (p4 → (p1 ∨ (p1 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199276070425889470137458321722 : (((((p1 ∧ p2) ∨ (p4 ∨ True)) ∧ p3) ∨ p2) → ((p2 → (p3 ∧ ((False ∧ p4) ∨ ((((p5 ∨ False) → p4) ∨ (True ∧ False)) → p4)))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316700120295364071955705772841 : (p3 ∨ (p5 ∨ (((False → p1) → p2) ∨ ((p5 ∧ p2) ∨ (True ∨ ((((True ∨ (p3 → (False → (p1 ∧ (True → False))))) ∨ True) ∧ p3) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184852296157057717244104143188 : ((((p1 ∧ p2) ∧ p2) ∧ (False ∧ (True → (p1 → (p4 ∧ p2))))) ∨ (p5 ∨ ((((p2 ∨ True) ∧ (False → p4)) ∨ False) ∨ (p1 ∨ (p5 → p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327797603020635191945857417264 : (True → (((p5 ∨ (((((p2 → p5) ∧ p5) ∨ (p1 ∧ p4)) ∧ (p4 ∧ p2)) ∨ (p1 → (p1 ∨ ((False → p1) → p1))))) ∧ False) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49683894547391100976391218310 : ((((p2 → p2) ∧ (p4 → ((((p5 ∨ p4) ∧ p3) → True) → ((((False → p5) ∨ False) ∨ (p5 ∧ p5)) ∧ True)))) → (p3 ∧ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724922671193548911062915743325 : ((((p5 ∨ (False → True)) ∧ (p2 ∨ (p2 → (((p3 → ((False ∧ (p4 ∧ (p3 ∧ ((p1 ∨ p1) ∨ p2)))) ∨ p2)) → p3) → (p5 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337564044883876742026726759460 : (p1 → (((((p2 → p1) ∨ (p2 → (p4 ∨ False))) ∧ (((p5 ∧ p5) ∧ (p5 ∨ p3)) → (p2 → True))) ∧ True) → (((True ∨ p4) → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217108662350303515885145634687 : ((((True ∨ p5) ∨ p4) ∨ p1) → (((p4 ∧ ((((p5 → p1) ∨ p4) ∧ p2) ∨ p2)) ∧ (False → p1)) ∨ (True ∨ ((p5 → (p5 → True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38268991994156635847573168549 : (((((((False ∨ (((False ∧ ((p4 ∧ p1) → (True ∨ p4))) ∨ p5) ∨ True)) ∨ True) ∧ False) ∨ p2) ∨ ((p5 → (p3 → p4)) → p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180607679918195869941950477562 : ((((p2 → (True → (True ∧ p2))) → False) ∧ (p1 ∨ ((p2 → False) ∧ p1))) → (p5 ∧ (((p1 ∨ p4) → ((p1 ∧ False) ∧ (p3 → p4))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (True → (True ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p2 → (True → (True ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h12
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h30
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h1.left
    let h33 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
      have h35 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- Implications on the right can always be decomposed.
        intro h37
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h32, we can now drive its conclusion.
      let h38 := h32 h35
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
      have h42 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h32, we can now drive its conclusion.
      let h45 := h32 h42
      -- False on the left can always be used.
      apply False.elim h45
  case inr h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h49 =>
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h50 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h51
        -- Implications on the right can always be decomposed.
        intro h52
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h51
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h53 := h47 h50
      -- False on the left can always be used.
      apply False.elim h53
    case inr h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h54.left
      let h56 := h54.right
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h57 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h58
        -- Implications on the right can always be decomposed.
        intro h59
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h58
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h60 := h47 h57
      -- False on the left can always be used.
      apply False.elim h60
  -- Implications on the right can always be decomposed.
  intro h61
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h62 =>
    -- Conjunctions on the left can always be decomposed.
    let h63 := h1.left
    let h64 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h65 =>
      -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
      have h66 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h67
        -- Implications on the right can always be decomposed.
        intro h68
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h67
      -- We have shown the premise of h63, we can now drive its conclusion.
      let h69 := h63 h66
      -- False on the left can always be used.
      apply False.elim h69
    case inr h70 =>
      -- Conjunctions on the left can always be decomposed.
      let h71 := h70.left
      let h72 := h70.right
      -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
      have h73 : (p2 → (True → (True ∧ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h74
        -- Implications on the right can always be decomposed.
        intro h75
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h74
      -- We have shown the premise of h63, we can now drive its conclusion.
      let h76 := h63 h73
      -- False on the left can always be used.
      apply False.elim h76
  case inr h77 =>
    -- Conjunctions on the left can always be decomposed.
    let h78 := h1.left
    let h79 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h79
    case inl h80 =>
      -- One of the premise coincides with the conclusion.
      exact h77
    case inr h81 =>
      -- Conjunctions on the left can always be decomposed.
      let h82 := h81.left
      let h83 := h81.right
      -- One of the premise coincides with the conclusion.
      exact h77
  -- Conjunctions on the left can always be decomposed.
  let h84 := h1.left
  let h85 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h85
  case inl h86 =>
    -- We want to use the implication h84 based on <expert-advice>. So we show its premise.
    have h87 : (p2 → (True → (True ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h88
      -- Implications on the right can always be decomposed.
      intro h89
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h88
    -- We have shown the premise of h84, we can now drive its conclusion.
    let h90 := h84 h87
    -- False on the left can always be used.
    apply False.elim h90
  case inr h91 =>
    -- Conjunctions on the left can always be decomposed.
    let h92 := h91.left
    let h93 := h91.right
    -- We want to use the implication h84 based on <expert-advice>. So we show its premise.
    have h94 : (p2 → (True → (True ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h95
      -- Implications on the right can always be decomposed.
      intro h96
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h95
    -- We have shown the premise of h84, we can now drive its conclusion.
    let h97 := h84 h94
    -- False on the left can always be used.
    apply False.elim h97



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113245569432865385906944574192 : ((((False ∧ ((False ∧ (False → (((p5 → ((p1 ∧ False) → p2)) ∨ (p2 ∧ p1)) ∧ p3))) ∧ True)) ∧ (p3 ∧ p1)) ∧ (False ∨ p4)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325636209739970693685524571874 : (p5 ∨ (False ∨ (((((p3 → p2) ∧ False) ∨ p5) ∧ ((p4 ∨ p4) ∧ p3)) → (((((p3 → True) ∧ p3) ∧ p2) ∨ p4) → (False ∨ (p4 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h20.left
      let h26 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181253460980194178409636104529 : ((p4 ∧ (((p5 ∨ (p4 → (p1 ∨ p5))) ∨ (p2 ∨ (p4 → p4))) ∧ p3)) → ((p1 ∨ p4) ∧ ((p3 → True) ∧ ((p5 ∨ p5) ∨ (p2 → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762071460174422716784309038587 : (((p3 ∧ (((((p1 → (p2 → (p2 ∧ p1))) ∧ p3) → (p2 ∧ (True → (p2 ∧ (False ∨ (p4 ∨ (p1 ∨ p4))))))) → p3) ∧ (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249410815737287274575610347312 : ((p5 ∨ False) ∨ (((False ∨ ((True ∧ ((p3 → ((False ∨ (p2 ∧ p2)) → (((p3 ∨ True) ∨ False) → p5))) ∨ p1)) ∨ (False ∧ False))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764691323709563745703562649736 : (((p4 ∧ ((p3 ∧ (((False → (((p4 ∧ p5) → False) ∨ p2)) → ((p4 → (p5 ∧ (p1 ∨ (True ∧ (False → p5))))) ∨ True)) ∨ p2)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39647671080587644746011610234 : (((p3 ∨ ((((p4 ∧ False) → (p4 ∨ ((p3 → p5) ∧ p2))) → p2) ∨ ((p1 ∨ ((p4 ∧ (True → p5)) ∨ (True ∨ False))) ∨ p2))) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102874613410242157578096524767 : (((((((((p5 ∧ True) → ((((True → p5) ∨ p4) → p1) → (p5 → p5))) → p4) ∨ p4) ∨ p3) → p4) → (False ∧ False)) ∨ True) ∧ (p1 ∨ True)) := by
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
theorem thm_5_vars_196829491041412667301421351957 : (((p2 ∧ (p3 ∧ ((p1 ∧ p1) ∨ p4))) ∧ p5) ∨ (p5 → ((p4 ∧ p5) → (True ∨ (((True ∧ p5) ∨ (p2 ∨ (True ∨ p1))) ∧ (p5 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810360723697749560212999529379 : (((p5 → (((True → p2) ∨ ((p5 ∨ p2) → ((True → False) ∨ False))) ∨ (((p2 ∧ True) ∨ ((p1 ∧ (p1 ∧ p5)) → (p5 → p3))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44067119045657506454491895934 : (((((p5 ∧ (False ∧ (p2 → ((False ∨ (((True → (p5 ∧ (p2 → p2))) ∧ p2) ∧ p3)) ∨ True)))) → p5) ∧ (False ∨ (p3 → p1))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776115429434519373245149789371 : (((p1 ∨ ((((((((p3 → p3) → (p3 ∨ False)) ∧ ((p3 ∨ (p3 ∧ p1)) → p5)) → p2) → p3) → (p2 ∧ (False ∨ p1))) ∧ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65370941087090226108046981679 : ((p3 ∨ ((p2 ∧ (True ∧ (((p3 → p4) ∧ p1) ∨ (p5 → True)))) ∧ (((((p4 → p2) → p1) → (False ∨ p3)) ∧ (True ∨ False)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174351934837535008769681883531 : (((((p3 ∧ False) → True) ∨ ((p3 → (p5 ∨ p3)) ∧ True)) → (p3 ∧ (False ∨ p1))) → (((True ∧ p3) ∨ p1) ∨ (p3 ∧ (False ∧ (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ False) → True) ∨ ((p3 → (p5 ∨ p3)) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601359388568523852844735739259 : ((((p2 ∧ (False ∧ ((((p2 → ((False ∨ (p3 ∧ p3)) ∨ True)) ∧ (p1 ∧ p5)) ∧ p4) → (p3 ∧ (((p3 → p3) → False) ∨ p1))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340526578401841877608741729628 : (p2 → ((((p4 ∨ p1) ∨ False) ∨ (((True ∨ (False ∨ p2)) → ((p4 ∨ p4) ∧ p2)) ∨ ((False → (p4 ∨ p4)) → ((p3 ∧ p5) ∨ True)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_197510087784437141210222539895 : (((p5 ∨ (p2 ∧ (p2 → p4))) ∧ (p3 ∧ p2)) ∨ ((p5 ∧ p5) ∨ (True → (p2 ∨ (p3 ∨ (((p4 ∨ False) ∨ (False → p3)) → (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706791228341122830225973170567 : ((((((p4 ∧ False) ∧ (p4 ∧ (p3 → p5))) ∧ p1) ∨ (p1 ∨ ((((p2 ∨ (p1 ∧ True)) ∧ p3) → p3) ∨ ((p1 → (p4 → p2)) ∧ p1)))) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317640324723783308505058147123 : (p4 ∨ ((((True ∨ False) → ((p4 ∨ ((True ∨ p1) ∧ p4)) → (((p5 → ((p2 ∨ p4) ∨ True)) ∨ p5) → (False ∧ (p4 → p1))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248470479850233687887125421653 : ((p2 ∨ p5) ∨ ((p4 ∧ (True → False)) ∨ (p3 ∨ (p4 → (p5 → ((p1 ∧ ((p1 ∨ p4) → ((p5 ∨ p2) ∨ ((True ∧ p5) ∧ True)))) ∨ p5)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304995837862908126297272003879 : (p1 ∨ ((((p1 ∨ (p1 ∧ (((p4 → ((p5 ∨ True) ∨ (False → p4))) → p1) ∧ p3))) ∨ (p2 → p4)) ∨ (p1 ∧ False)) ∨ (p4 → (False → False)))) := by
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
theorem thm_5_vars_317705368821642588349200207423 : (p4 ∨ ((((p1 ∨ (p2 → ((p2 ∨ ((True → (p1 ∧ (p1 → p3))) → True)) ∧ ((p5 → (p4 → p3)) → p2)))) → p3) ∨ (p1 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152575314668881027470750979879 : (((False → (p2 ∧ p2)) → (True ∧ ((p3 ∧ (((True → False) → (p4 ∧ True)) → ((p5 ∧ p3) ∨ p5))) ∧ p4))) → ((False → True) → (p3 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p2 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (False → (p2 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185153481752049102124721167717 : (((p2 ∨ p5) → ((p3 ∧ (p4 ∨ p5)) ∧ ((p1 ∨ p2) → p3))) ∨ (((False ∨ (p4 → (p4 ∧ (p5 ∨ p4)))) ∨ (p3 ∧ (p4 → p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184727142768610345049440265146 : (((True → ((p5 ∧ p1) ∨ (p4 ∧ p5))) → (False ∧ (p3 → p2))) ∨ (p4 → ((p3 → (((p1 ∨ True) ∨ p1) → ((p2 ∧ p3) → p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8718343496772116488978344893 : ((((p5 → (p2 → ((True → (p1 ∧ p2)) ∧ (((p2 → p4) ∨ p3) → (p3 → (p5 ∧ ((p2 ∧ p2) ∧ True))))))) → (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224071358646107728941490369920 : ((p5 ∨ (False ∨ True)) ∧ ((((p3 ∨ p5) ∧ False) ∧ (((p5 ∧ p2) ∧ p1) → True)) ∨ (True → (((p3 → p3) ∧ (p4 ∧ False)) → (True ∧ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148460653424142436942920131196 : (((((p1 ∨ p5) ∨ (p4 ∧ p2)) ∨ ((p5 ∨ (p1 → p3)) ∧ False)) ∧ (((p4 ∧ False) ∧ (False ∧ p4)) → p3)) ∨ (False → ((False ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110109097634985821706168496424 : ((p1 → (((p5 ∨ (p3 ∧ ((((False → (p2 ∨ p3)) ∧ ((p3 ∨ p1) ∨ (p2 ∧ p4))) ∧ p3) → p2))) ∨ (True → True)) ∧ p1)) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110928069318785176198092124458 : ((((((p2 → ((p3 → p1) ∧ ((((False ∧ (p5 → p2)) → p2) ∧ False) ∧ p5))) → (p3 → p1)) ∧ p1) ∧ (p2 ∨ p2)) ∧ p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157925526795942663860927617877 : (((((False ∧ p3) ∨ (p3 ∨ (p4 ∧ p5))) ∧ p3) ∧ (((p2 ∧ p1) ∨ (p3 → p4)) → (p2 → p5))) ∨ (((False → p2) ∨ (p4 → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315811456014009120165973388143 : (p3 ∨ ((p2 ∨ True) → ((((p2 ∧ p3) ∧ (p5 ∨ p4)) ∧ p2) ∨ (((p3 ∧ (True ∨ p2)) → ((p3 ∧ (p2 ∧ (p3 ∨ True))) → False)) ∨ True)))) := by
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
theorem thm_5_vars_314651277595937386579889772064 : (p3 ∨ (((False ∧ (p1 ∨ (((p1 ∨ p4) ∧ p3) ∨ (p3 ∧ p5)))) ∨ (p2 → (p5 ∨ p2))) ∨ ((p2 ∧ p5) → ((True ∨ (p4 ∨ p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620355928847515933870343104167 : (((((p2 ∨ p4) ∨ ((((False ∧ (p1 ∧ p2)) ∨ (p1 → (p4 ∨ ((p2 ∨ True) ∨ p1)))) ∧ (p5 ∧ (False ∨ p1))) ∨ (False → True))) ∨ p1) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621837125838426757457975372127 : ((((p1 ∧ ((((p1 → p1) ∨ p4) ∧ ((False ∨ True) ∨ (p1 → ((p5 ∨ p3) ∧ False)))) → ((p4 → p2) → (p5 ∨ (p4 ∧ False))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_107467569244701718929777302626 : (((p2 ∧ (p4 ∨ p5)) → (p4 ∨ ((p4 ∨ (p5 ∧ ((((p3 ∨ p5) ∨ (p1 ∨ p4)) → False) → (True ∧ False)))) ∧ (True ∧ p5)))) ∧ (p4 ∨ True)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ p5) ∨ (p1 ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233748762440223394220653692385 : ((p3 ∨ (True ∨ True)) → ((((((p3 ∨ False) ∧ p5) → p3) → False) ∧ p2) ∨ ((p1 → ((p4 ∧ False) → (p3 → ((p4 ∨ p3) → p4)))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_317683039740326044955168067923 : (p4 ∨ (((p4 ∧ ((p3 → (p3 → (((p2 → (p4 ∧ p2)) ∧ ((p3 ∧ p1) ∧ (False ∧ ((p1 ∧ p4) → p1)))) ∧ True))) ∧ True)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



