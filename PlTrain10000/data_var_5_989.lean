variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302508817842583693698241408880 : (False ∨ (False ∨ ((((((p5 ∧ p5) ∨ p5) → True) ∧ (p4 ∨ p5)) ∨ (p1 ∧ ((p4 → (p3 ∨ p5)) → (p4 ∧ (p5 ∧ False))))) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_41460597099301399736310327048 : (((((p5 ∧ True) → (((p3 → (False ∨ False)) → (p3 ∧ p2)) ∨ p1)) ∧ (((False ∧ (p4 ∨ (False → (True ∨ p2)))) → p2) ∧ p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37378105774330058211692908634 : ((((((((p1 ∧ (p4 ∨ True)) → (p2 ∧ (p4 ∧ ((((p5 → (p4 → p2)) ∨ p2) ∧ p4) → False)))) ∨ p5) → p3) → False) ∨ p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48962763501330041193177496272 : (((((p4 ∧ (p4 ∧ ((((((p1 ∧ (p5 ∧ True)) ∨ (True ∧ True)) → False) ∧ p4) → p2) ∧ p4))) ∧ False) ∨ False) ∨ ((True → True) ∨ p4)) ∨ p3) := by
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
theorem thm_5_vars_248889500128855264103054119140 : ((p3 ∨ p5) ∨ (((p2 ∨ (False → (False → p5))) ∨ (p5 ∨ p3)) ∧ (p3 ∨ (p5 → ((True ∧ (p1 ∧ (p5 ∧ p2))) ∨ (p4 ∨ (p5 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55435074815554338566872830199 : (((((p4 → (p4 → False)) ∧ True) → p4) → (p4 ∨ (p2 ∨ ((p3 → False) ∨ (False → ((p1 ∧ (p2 ∨ ((p2 ∧ p1) ∨ p4))) ∧ p1)))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135966732047805214556743746315 : (((True → (False ∨ ((p4 ∨ p3) ∧ ((p5 ∨ p1) → p1)))) ∧ ((((p5 ∨ False) ∨ (p4 ∧ (p4 ∧ True))) → p5) → p2)) ∨ (p3 → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318384517435906712592981663300 : (p4 ∨ ((True → (((p2 → p5) ∨ ((p1 ∨ (p2 → (True ∨ True))) ∨ ((p1 ∨ (p4 ∧ p4)) ∧ ((p1 → False) ∨ (p2 → p4))))) ∧ p4)) → p4)) := by
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
theorem thm_5_vars_47462846610069583353485514987 : (((p5 ∧ ((True ∧ (((p3 ∧ (((p1 ∧ p2) ∧ p4) ∨ ((p2 → (p4 ∨ p2)) ∧ p1))) ∧ p1) ∧ (False ∧ False))) ∨ p5)) ∨ (p5 → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37441411217097347768972551380 : (((((p1 ∨ (False ∨ ((((True ∧ p2) ∨ (p1 → True)) ∧ (p4 ∧ (p5 ∧ p2))) ∨ False))) → (((False ∨ p2) ∧ p5) ∨ p1)) ∨ False) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h8.left
          let h13 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h8.left
          let h18 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245367530541213915413475852675 : ((p2 ∧ p3) ∨ ((((p1 ∨ p1) → ((p4 → p5) → p2)) ∨ p5) ∨ (((p3 ∧ p5) ∧ (p5 → ((p1 ∨ ((p1 ∨ True) ∨ p1)) ∨ p5))) → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63275769607593584089680032611 : ((p5 ∧ ((p5 ∧ ((p1 ∨ p1) → p2)) ∧ (((((p3 → False) → ((False ∧ True) ∧ False)) ∨ False) → (p2 → False)) ∨ ((False ∨ p4) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647538056967773320094728074477 : ((((p5 → ((((p2 ∨ p2) → (((False ∧ p5) ∨ False) ∨ ((p1 ∧ p2) ∨ p1))) → (p3 ∨ ((True → (p3 → False)) → False))) ∨ p5)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791314424417552294715434730598 : (((True → (((((p2 → (p5 → ((p3 ∧ (((p5 ∧ p2) ∧ p1) ∨ True)) → p2))) ∨ (((p5 → False) ∧ p1) ∨ False)) ∨ p1) → False) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_317738101863593389317807750373 : (p4 ∨ (((((((p4 ∧ True) ∨ ((False ∨ (p1 → True)) ∧ (p3 → ((p2 → False) → False)))) ∧ p5) ∧ p3) → p4) → (True → (True → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592512172079248617350061029339 : ((((((p2 ∧ p4) ∨ (((((p4 ∧ ((True → p2) ∨ p5)) ∨ p5) ∨ p4) ∧ (p3 ∧ (True ∧ p5))) → (p5 ∧ p1))) → (p4 ∧ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187754581627112889668148659559 : ((p2 → (((p2 ∨ p4) ∨ ((p2 ∨ p3) ∧ p1)) ∨ (p1 → p1))) → (((p1 ∧ p1) ∧ (p4 ∨ p2)) ∨ (p4 ∨ (p3 → ((p3 ∨ p5) ∨ True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63360110435214934040419341447 : ((p5 ∧ (p2 ∧ (p5 → (((p5 → ((True → (p4 → p1)) ∨ False)) → ((False → p1) → False)) → ((p2 ∨ True) → (p3 ∧ (p4 → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330281609562015962981168268377 : (True → (False ∨ (p4 ∨ (((((p1 ∧ False) ∨ True) ∧ p2) → ((((((p1 ∨ p5) → (p2 ∨ p5)) → p5) ∨ p2) ∧ p5) ∨ True)) ∨ (p1 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146932674343434547880326905422 : ((((((((p1 ∧ p3) ∨ (((True ∨ (p2 ∨ p2)) ∧ p5) ∨ (p4 → p3))) → p5) → p4) ∧ True) ∨ p5) ∧ p1) ∨ (p3 ∨ ((p3 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742795102755279752439805637765 : ((((p3 → p1) ∨ (((((True ∧ False) ∧ True) ∨ p3) ∨ ((p4 → (p1 ∨ ((p1 ∨ (p3 ∧ p5)) ∧ (p4 ∨ (p2 ∧ True))))) ∨ False)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14583264716839303809208134481 : ((((p3 ∨ (p2 ∨ (p5 ∨ ((p3 ∨ (False ∧ (p5 → p5))) ∨ ((p4 → False) ∧ (p2 → (True → (True → p4)))))))) ∨ True) ∨ (p4 → p1)) ∧ True) := by
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
theorem thm_5_vars_137766267234939919676725456897 : ((p2 ∨ (((p5 ∨ (((p4 → p3) ∨ p3) ∨ (p5 → (p2 → (p2 ∨ (p5 ∧ p4)))))) ∧ p2) ∧ ((p2 ∧ p2) ∨ p5))) ∨ (False → (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746981362087278671758150835565 : ((((p4 ∨ p2) → ((((p5 → (p2 ∨ p3)) ∨ p5) ∨ ((p5 → p5) ∧ False)) ∨ ((p5 ∨ p3) → (p1 ∨ (p1 ∨ (True ∨ (p1 ∨ p2))))))) ∨ p4) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595267164422946532871237006697 : (((((((p2 ∧ (True → False)) ∨ ((p1 ∨ p3) ∨ (p2 ∧ p5))) ∧ p2) ∧ ((((p4 → p5) ∧ False) → p3) → ((p3 ∧ p4) ∨ p4))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218902030165862748704051003207 : ((p3 ∧ ((True ∨ p4) ∨ p5)) → ((((False ∨ p1) ∨ ((((p2 ∨ p4) ∨ True) ∧ p5) ∧ p5)) ∨ p3) ∧ ((p5 → (p1 ∧ (p1 ∧ p3))) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686109511208841569152762100733 : ((((((p2 → (((p5 ∨ p1) ∧ p1) ∨ (p4 ∨ (True ∧ p1)))) ∨ True) ∨ ((p5 ∧ p1) → p1)) → (p3 ∨ (((p2 → p1) → p3) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219982886710636083071646366997 : ((p5 → (p2 ∧ (p1 ∧ False))) → (((False → (p3 ∧ ((p3 ∨ p1) ∨ (((p5 ∧ False) ∨ p3) → p2)))) → (((p1 ∧ p3) ∨ p5) → p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658600831360660346334261602391 : ((((p3 ∨ ((((p5 → ((p5 → (p5 → (p3 ∧ p1))) ∧ (p5 ∧ p5))) ∨ ((p2 → p1) → False)) ∨ False) ∨ (True ∨ p4))) ∨ (p2 → p5)) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302986588799466493244012924998 : (False ∨ (p1 → ((p5 → (((p5 → True) → ((((p5 ∧ p4) → p5) ∨ (p3 → (p4 ∧ (p2 ∧ (p5 ∨ p2))))) → (p3 → p4))) ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936898757415431950990412068689 : ((((((p3 ∨ (p5 ∨ p2)) ∨ False) → False) ∧ (p2 ∧ (True ∨ ((p1 → (p1 ∨ (p4 → ((((p2 ∧ True) ∨ p5) ∨ p5) ∨ True)))) ∨ p2)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ (p5 ∨ p2)) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∨ (p5 ∨ p2)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 ∨ (p5 ∨ p2)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58973678901409286754122632389 : (((p2 ∧ p4) ∨ (((True → (((p3 → p5) → ((False ∧ True) ∨ (p4 ∧ True))) ∨ (p4 ∧ ((True ∧ False) ∧ p3)))) ∧ (p5 → p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162899445773517340290745729937 : (((p4 → (((p2 ∧ (((False ∧ p4) ∧ True) ∨ p5)) → (True ∨ p2)) → p2)) ∨ (p3 → True)) ∧ ((p5 ∨ p4) ∨ (p2 → ((False → True) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180782710594856394166370565774 : ((((p2 → p1) → (p3 ∧ p5)) → (((True ∨ (p5 ∧ p5)) → p4) → p3)) → ((False ∧ (p2 ∧ p3)) ∨ (True ∧ (False → ((p4 ∨ p4) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137844661008888734532435454960 : ((p3 ∨ (((p1 → (p4 ∨ True)) ∨ (True ∨ False)) → ((p5 → (p3 ∧ p5)) ∨ ((((p1 ∨ True) ∨ False) ∨ False) ∧ True)))) ∨ (False ∧ (p3 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246715512068021123736320168002 : ((p5 ∧ p4) ∨ (True ∧ ((((False → p4) ∧ (p4 ∨ (True ∧ ((False ∧ (True → p5)) ∨ p4)))) ∧ (p2 → ((p5 ∨ p1) ∨ False))) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_136355800646316487852405071748 : (((p5 → (True → (p2 ∨ False))) ∧ (((((p4 ∨ p5) → p3) → ((True → p4) → (False ∨ p5))) ∧ p1) ∧ (True ∨ p5))) ∨ (p3 → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621306508803973033775247263827 : ((((True ∧ ((True ∨ ((p4 ∨ (p5 ∧ p3)) ∧ (p1 ∨ p1))) → ((p4 → (p5 ∧ p3)) ∧ (p5 ∧ ((p1 ∨ (True → p5)) ∧ p2))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_242584766283387917761437518810 : ((p3 → True) ∧ ((p1 ∨ p1) → ((p2 ∧ ((p3 → p4) ∧ p3)) ∨ ((((p5 → True) → (p4 ∨ p4)) ∨ p3) ∨ ((False ∨ (p4 ∧ p4)) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345639957929329380484493229687 : (p3 → ((p2 ∧ (p4 ∧ (p1 ∧ (((p1 ∨ False) ∨ ((p2 ∧ True) ∧ (False → ((False ∧ p3) → ((False → p1) → (p5 → False)))))) ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734729122724785691718621471352 : ((((p2 ∨ True) ∧ ((((p5 → (((p1 → p3) → p1) ∧ p2)) ∧ ((p5 ∧ (p2 ∨ p2)) → p5)) → (False ∧ ((True ∧ p2) ∧ p3))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55817667095834326438974671070 : ((((p4 ∨ p1) → (p1 → p1)) ∧ (p3 ∨ (p2 → ((p4 ∨ ((p3 ∨ p5) ∧ ((p1 ∨ p1) ∧ p2))) ∨ (p2 → ((p4 ∧ False) → p5)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159320568352486147387198048736 : ((p5 → (((p4 ∧ (p2 ∧ p3)) ∧ (p1 → p4)) ∨ ((p4 → p3) ∨ ((True ∧ (p3 ∧ p2)) → False)))) ∨ ((True → True) ∧ (p2 → (p5 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352816642530763346292985490917 : (p4 → ((p5 ∨ p4) → (((p2 ∧ (p2 ∨ (True ∧ (p5 → ((p5 → False) → False))))) ∨ (p3 → p5)) ∨ (((p5 ∧ p4) ∨ False) ∨ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43800528314253725176469129690 : ((((True → ((True → (False ∨ False)) ∧ (((p1 → p4) ∧ p5) ∨ (p1 → (p3 → (((p2 → p1) → p3) ∧ (p3 ∧ p5))))))) → p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668788431313701155219022087912 : (((((((((p3 ∧ p3) ∧ p5) → True) ∨ (p5 → (p1 ∨ (((False ∨ p4) → False) → p4)))) → (p3 → p2)) ∨ False) ∨ (p2 ∨ (p2 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48954044487505790339942510049 : ((((p3 ∨ (p1 ∨ (((((False → p3) ∧ (p2 → (p4 → ((p1 ∨ p5) ∧ p5)))) ∨ False) ∨ p3) ∧ False))) ∧ True) ∨ (p5 → (False → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780171579438837209120452193910 : (((p2 ∨ ((p1 ∧ ((True ∧ (True → (((True ∨ False) ∧ p3) ∧ ((p5 ∧ p3) ∨ p1)))) → ((p1 ∧ p1) ∧ True))) ∧ (p3 → (p2 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638626273676051538609262129536 : ((((((((p2 ∧ p3) ∨ False) ∨ p5) ∧ p1) → ((((True ∨ p5) ∨ (False ∨ False)) → p5) ∧ ((True → ((False → False) → p2)) ∨ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156631743625530772497627983940 : (((((p3 ∨ (p1 ∧ False)) ∨ (p3 ∧ ((p2 → (p2 ∧ ((p5 ∨ p4) ∧ p1))) → p4))) ∨ p4) ∧ p4) ∨ ((p4 → ((p3 ∧ True) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192569893512258566308242847293 : (((p4 ∨ ((((True → p2) ∧ True) ∧ p3) ∧ p4)) ∨ False) → (p3 → (((p4 ∧ ((p4 → p4) ∧ (p3 → False))) ∨ (False ∨ p5)) ∨ (p3 ∨ p5)))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324753325759516395844921614810 : (p5 ∨ ((p5 ∨ (p1 → False)) → ((((p4 → ((((True ∨ p1) ∨ True) → p2) ∨ p1)) ∨ ((p4 ∧ p5) ∨ ((True ∧ p5) ∨ True))) ∧ p1) ∨ True))) := by
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
theorem thm_5_vars_175314645145094959393781095939 : ((p4 ∨ (((True → False) ∧ ((p2 → ((True ∨ p4) → (True ∨ p5))) ∧ p1)) → p5)) → ((p1 → ((((p3 ∨ p3) → p2) ∧ p5) ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_148555561035392116111037260232 : (((((False ∧ (p5 ∧ p5)) ∨ (p2 ∧ False)) ∨ (p3 → p3)) ∧ (((p3 ∨ (p1 → p5)) → (p5 ∨ False)) → p5)) ∨ ((p1 → (p5 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674098443864261649048639524834 : ((((p2 ∧ ((p3 ∨ p3) ∧ (((p5 ∨ True) ∧ (p2 → ((((True ∧ p5) ∧ p5) ∧ p2) ∨ p3))) ∨ (True ∨ p1)))) → (p4 ∨ (p4 ∨ p2))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321132144859199174349460429045 : (p4 ∨ (p2 ∨ (((p5 → p5) ∨ (True ∨ ((False ∨ p4) ∨ (p1 → (p5 ∧ (p2 ∨ p3)))))) → (p3 ∨ (p2 ∨ ((p3 ∧ p3) → (p3 ∨ p3))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_963672859550312708756770099807 : ((((p3 → p4) ∧ (((p4 ∧ (False ∨ False)) → p5) ∧ ((p3 → False) ∧ (((p2 ∨ (p2 ∧ p1)) → ((p3 ∨ p4) ∧ False)) ∧ (True ∧ p2))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : (p2 ∨ (p2 ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149959040934713330581350510177 : ((p4 ∨ ((((p3 → (False ∨ p3)) ∧ True) → ((p1 ∧ (False ∧ (p1 ∧ p5))) ∨ (False → (p4 ∨ p5)))) ∨ p4)) ∨ (((True ∨ True) ∧ True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58788700451041934644185178831 : (((p5 → True) ∧ (((p1 → ((p4 ∨ ((p3 ∨ ((p2 ∧ True) → True)) ∧ (p1 ∨ p2))) ∧ p4)) ∧ (((p3 → p2) → p2) → p1)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166040987589794282682464897296 : (((p4 → False) ∨ (((p2 → (p3 ∨ ((False ∧ p3) ∨ p1))) → (p3 ∨ (p4 ∨ p2))) ∨ p1)) ∨ ((p4 ∧ (p2 ∧ (p5 ∨ p3))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263832336887631417869016476528 : (True ∧ (((False → ((False ∨ p2) → (p2 ∧ (p2 ∨ p2)))) → (((p3 ∧ p5) ∨ p3) → p4)) → (p2 → ((((False → False) → p5) → p5) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431149599765120028686276290264 : (((((True → False) → ((True ∨ p3) → ((p4 ∧ ((False ∧ ((p5 ∧ (p5 ∨ True)) ∨ False)) → p1)) ∨ ((False ∨ p3) ∧ True)))) ∨ (p4 ∧ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148134107261122890529021252692 : ((((p3 ∨ p4) → ((((True ∧ True) ∨ (p2 → p5)) → (p5 ∧ p1)) ∧ (p4 → (p4 ∨ p4)))) → (p2 ∨ p4)) ∨ ((p4 ∨ False) → (False ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306558112172515155089747096766 : (p1 ∨ ((False ∨ p4) → ((((((p5 ∧ False) ∧ p5) → p3) → p1) ∨ True) ∨ (((p5 ∨ False) ∧ p5) ∨ (False → ((p4 → (p5 → p5)) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184477757188828489064377236107 : ((((p5 ∧ ((p3 ∨ (p2 ∨ False)) ∨ p1)) ∨ p2) ∨ (p3 → p3)) ∨ (((p2 ∧ (True → (p5 → ((True ∨ p5) ∨ p3)))) → True) ∧ (False ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303064495305356770090645390840 : (False ∨ (p2 → (((((p5 → False) → (p5 ∨ p3)) ∧ (p4 → p5)) ∨ (p1 → (p1 ∧ p5))) ∨ (((((p2 → False) → p4) ∧ False) → p5) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135036412142486814613891947258 : (((((p4 ∧ ((p5 ∨ False) → p5)) ∨ (p1 ∧ ((False ∧ p2) ∨ ((True → p5) ∨ (p5 ∨ p3))))) ∧ p5) ∨ (False → p5)) ∨ (p1 ∧ (True → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720409105257667357265020063742 : ((((((p4 → p2) → p5) ∨ p3) → ((((p2 ∧ p2) ∨ (p2 ∧ p4)) ∧ p3) ∨ (p1 ∨ (False ∧ (((True ∧ True) ∨ (p1 ∨ p5)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49108437297357486303502352015 : (((((True → ((p5 → False) ∨ p2)) ∧ (p2 ∧ ((p4 ∨ p4) ∧ (p3 ∧ p3)))) ∧ ((p4 ∨ (False ∧ False)) → p2)) ∨ ((p1 → p1) ∧ True)) ∨ False) := by
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
theorem thm_5_vars_698308446506755088097638741056 : (((((p3 ∧ ((p4 ∧ (True ∧ p5)) → (True → p3))) ∧ (False ∧ p5)) ∨ (p2 → (((p2 ∨ False) ∧ ((p3 ∨ p4) → p5)) ∨ (p5 → True)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245175789725797757054944696268 : ((p2 ∧ False) ∨ (((p5 ∧ ((((p1 ∨ (p5 ∧ (False ∧ p1))) ∨ p3) ∨ p2) ∨ ((p5 → p4) ∧ (p3 → p2)))) ∨ p1) ∨ (p3 ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588311892609134435892027594430 : (((((((p4 → True) → (True ∧ p1)) ∧ (((p3 ∨ p4) → ((p1 → p4) ∧ ((True ∧ p2) → (p4 ∧ True)))) ∧ (p3 ∧ True))) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168600211364188212498926470011 : ((p3 ∧ (((p4 ∨ p2) ∧ (((p2 ∨ p2) ∧ ((p4 → p2) ∧ p3)) ∨ (p4 ∨ p5))) ∧ p4)) → (((p5 ∨ ((p2 ∨ p1) ∨ p3)) ∨ p5) ∨ p3)) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h11.left
        let h17 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h24.left
        let h30 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175366362507361768265932497305 : ((p5 ∨ (p4 → (p4 → ((p4 ∧ (p5 → (p2 ∨ ((p1 ∨ False) ∨ False)))) ∨ p1)))) → ((p5 → False) ∨ ((False → (p5 ∧ p4)) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8005480087389215640094231703 : ((((((p4 ∨ p2) → ((p5 ∨ ((True ∧ p2) ∧ p5)) ∨ ((p3 → ((p3 ∨ p1) ∧ p1)) ∨ ((p4 ∨ False) ∨ p2)))) → p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214301261283490907308875371906 : (((p5 ∧ (p4 → p2)) → p4) ∨ ((p3 ∨ False) → ((((p3 → True) → (p5 ∨ False)) ∨ ((p1 ∧ p3) ∨ True)) ∨ ((p5 ∨ p1) → (p5 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43926979796939774501494145303 : (((((False → ((p2 ∨ (p5 ∨ p1)) ∨ (p5 ∨ ((((False → p4) → p3) ∧ (p4 ∧ p4)) ∨ p1)))) ∨ (p1 → p5)) ∨ (True → p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789709503774631451531489083009 : (((p5 ∨ (((p1 → (p5 ∧ p1)) ∨ p1) ∧ ((p1 → False) → ((True → (((p4 → p1) ∧ (p5 ∧ False)) ∨ (p2 ∧ p4))) ∧ (True → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49765795865187915164606346735 : (((False ∨ (True ∨ (True ∨ (p2 ∨ (((p4 → ((p4 → p1) → p4)) ∧ ((p4 ∧ p4) ∧ p3)) → (p2 → p3)))))) → ((p3 → p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45281849450215464436429322914 : (((p2 ∧ ((p1 → (((p3 ∧ (p3 ∨ False)) ∧ p2) → (((p3 → (False ∨ p5)) ∨ p2) ∨ p1))) → ((p2 ∧ (True ∨ p2)) ∧ p3))) → p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (((p3 ∧ (p3 ∨ False)) ∧ p2) → (((p3 → (False ∨ p5)) ∨ p2) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h4
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130627551420505459603266273203 : ((((((p2 ∨ (p5 ∧ (((p1 → p2) → False) ∨ False))) ∧ True) ∨ True) ∨ (p1 → p4)) ∨ (p2 → ((p4 ∨ p1) ∧ p5))) ∧ ((p1 → p1) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341817868723182336194171811305 : (p2 → ((((((p2 ∧ False) → (True → (((p3 → p4) ∧ True) ∨ True))) → (p1 ∧ p4)) ∧ (p1 → p5)) ∧ ((p4 ∨ p1) ∨ p1)) → (p1 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : ((p2 ∧ False) → (True → (((p3 → p4) ∧ True) ∨ True))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h9
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h25 : ((p2 ∧ False) → (True → (((p3 → p4) ∧ True) ∨ True))) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- False on the left can always be used.
        apply False.elim h29
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h30 := h20 h25
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h31
  case inr h32 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h33 : ((p2 ∧ False) → (True → (((p3 → p4) ∧ True) ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h34
      -- Implications on the right can always be decomposed.
      intro h35
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- False on the left can always be used.
      apply False.elim h37
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h38 := h20 h33
    -- We need to get the right conjuct of h38 based on <expert-advice>.
    let h39 := h38.right
    -- One of the premise coincides with the conclusion.
    exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190333071063128487972976263986 : ((((p4 ∧ (p5 → (p5 ∧ p5))) → (p3 ∨ p5)) ∨ True) ∨ (True ∨ ((((False → p1) → (((p5 → p1) → p1) → True)) ∧ (p2 ∧ False)) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56107547706600383513021318285 : ((((p3 → p3) ∧ (p3 ∧ p1)) ∨ (p1 ∧ ((((p5 ∨ p2) ∧ (((p4 ∧ p5) ∧ ((True → True) ∧ p5)) ∧ (p4 ∨ p3))) ∨ False) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142518418353224375403972384690 : ((True ∨ (((((p1 → False) ∨ (p2 → ((p3 ∨ p4) → (p5 → p4)))) ∧ True) ∧ (((p3 ∨ p4) ∧ p4) ∨ p5)) → True)) → ((p2 → p5) ∨ True)) := by
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
theorem thm_5_vars_586933389709383395870493655479 : (((((p2 ∨ (((p4 ∧ (p5 ∧ ((False ∨ ((p3 → (p5 → (p1 ∨ ((False ∨ True) ∧ p2)))) → p4)) ∧ True))) ∧ p3) ∨ p2)) ∧ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159095002693888167812015404421 : ((True → ((((p1 ∨ p4) ∨ (p5 → p4)) ∨ (p1 ∧ False)) ∨ (p5 → (((p2 → True) ∧ p2) → p3)))) ∨ ((p2 ∧ False) → (p4 ∧ (p2 ∧ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149095941071658406556573725390 : (((p1 ∨ (p3 ∧ p3)) → (((p3 ∨ p4) ∧ ((True ∧ p4) ∧ True)) ∨ (p2 ∨ (True ∨ (p4 → (p1 ∨ p3)))))) ∨ (p5 → (p3 ∧ (False ∨ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18836858578570181588919238633 : ((((True ∧ (False ∧ (((p1 ∨ p3) → False) ∨ (False → True)))) ∧ ((p4 ∧ p2) ∧ (False ∨ p4))) ∨ (True ∨ (True ∧ ((p1 ∨ True) ∧ True)))) ∧ True) := by
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
theorem thm_5_vars_307851897204897853428295444475 : (p1 ∨ (p5 → ((p3 ∨ ((p3 ∧ ((p5 → (((p5 ∧ p4) ∨ ((False ∧ p2) ∧ (p3 → p2))) ∨ p3)) ∧ True)) ∨ (p1 ∧ (False → False)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46558489072256606285179478825 : ((((p3 ∨ p2) → ((p1 ∧ (True → True)) ∨ ((p3 ∧ p4) ∨ (p5 ∨ (p4 → (((True ∧ (True ∨ p1)) ∨ p5) ∧ p2)))))) ∧ (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709286906997238106395478366474 : (((((p5 → p2) ∨ ((p3 ∧ False) ∧ (p1 → p1))) → (False ∧ ((False ∨ True) ∧ ((p5 ∨ ((False ∨ p3) → ((p3 → False) → p4))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112137432446761558973935278031 : (((False ∧ (p5 ∧ (((p2 ∧ ((p4 ∨ p2) → (((p3 ∧ p2) → ((p4 ∧ p3) ∨ p4)) ∨ p3))) ∧ (p1 ∧ p2)) ∨ p2))) ∨ True) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336442333576687185137845077208 : (p1 → ((p4 ∨ ((((False ∨ (True ∧ ((True ∧ False) ∨ (p1 ∨ (p5 ∧ (p3 ∧ p2)))))) ∧ p3) ∨ p5) ∨ (p1 → (True → (False ∨ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115332771840477381812548230230 : (((p3 ∧ (((p3 ∧ p5) ∨ p5) → ((p3 ∧ False) → p4))) → (((True ∧ p5) ∧ p1) → ((((p3 ∨ p1) → p1) → False) ∨ p1))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113042333816475220520584885577 : (((False ∨ (p5 ∨ (p5 ∨ (p4 ∨ (p2 → ((False ∨ (((((p5 ∨ p1) ∧ (p4 → p2)) → p1) ∧ p1) ∨ p1)) ∧ True)))))) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149547160178231556799238998007 : ((p2 ∧ ((True ∧ (p5 ∧ ((p4 ∧ (p4 ∨ ((False → p4) → p5))) ∧ ((p5 → p2) ∧ True)))) ∨ (p2 ∧ p3))) ∨ (p3 ∨ ((False ∧ p4) → False))) := by
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
theorem thm_5_vars_137846406762787183066003840837 : ((p3 ∨ ((p4 ∨ (p2 ∧ (p5 → True))) ∨ ((p1 → ((((p4 → (True ∧ p5)) ∧ p2) ∧ (True ∧ p4)) ∧ p3)) ∨ p2))) ∨ (p1 → (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709640887762157077452348335706 : ((((p3 ∨ (((True ∧ p2) ∨ True) → (True ∧ p1))) → ((p2 ∨ ((p4 ∨ (p2 → (p4 → (p2 → (p3 ∨ p1))))) ∧ (p2 ∨ p3))) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174053699752172289414650977048 : (((p2 → ((((p5 ∧ p1) ∨ (False → True)) → (p1 ∨ p2)) ∨ (False ∧ p4))) → False) → (p5 ∨ (p5 → ((True → (p4 ∨ False)) ∧ (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((((p5 ∧ p1) ∨ (False → True)) → (p1 ∨ p2)) ∨ (False ∧ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



