variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115365922266259665723983760918 : (((((p1 → ((p5 ∨ p2) ∧ p4)) → p5) → p2) ∧ (False ∨ (((True ∨ (True ∨ (((p1 ∧ p5) → p1) ∨ False))) ∨ p3) ∨ p1))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354384247241920426287684580758 : (p5 → (((((p5 ∨ False) → p3) ∨ True) → (p4 → ((p4 → False) → (p1 ∨ ((((((True → False) → p3) ∨ False) ∧ p1) → p5) → p3))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4008083537125636346046966472 : (p1 ∨ (p2 ∨ (((p4 ∨ (False ∨ p3)) ∨ (((p5 ∨ False) ∨ (p4 → p4)) ∨ (p5 → False))) ∧ ((((p3 ∧ p3) ∧ p2) ∧ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355862645159760503045015453215 : (p5 → ((((p1 → (((p1 → p1) ∧ False) ∧ p5)) ∨ False) → ((p2 → ((p1 ∧ (p3 ∧ False)) ∧ (False ∨ p2))) → False)) ∨ (p5 → (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156786127116064066996935696830 : (((p1 ∧ (((p4 ∧ (p1 → True)) ∨ ((True → (True → p4)) ∧ p5)) → (True ∧ (p5 ∨ p3)))) ∧ p3) ∨ (True ∨ (True ∧ ((False → True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134803226441360798015344624650 : (((p4 ∧ ((p2 → False) ∨ ((p3 ∧ False) → ((p4 → (((False ∨ ((True ∧ p5) ∨ p5)) ∨ True) → p5)) ∧ p2)))) → p5) ∨ (p1 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55683038821535142294692413306 : (((((p4 ∧ False) ∨ False) ∨ p5) ∧ ((p5 ∨ p3) → (False ∨ (((p2 → p3) ∧ ((False ∧ p1) ∧ (p1 → True))) → ((p1 → True) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614138439044978364204569716828 : ((((((((False → (p2 ∧ (p4 → ((p2 ∧ (p4 ∧ p3)) ∧ (p2 → (p2 ∨ True)))))) → p4) → p3) ∧ p2) → (True → (p3 → p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_168741486437722366432796455757 : ((False ∨ ((p2 ∧ (False ∨ (((p4 ∨ p1) ∧ (True ∨ False)) ∧ True))) ∨ ((p1 ∨ p2) → True))) → (False ∨ ((p2 ∧ p2) ∨ ((False → p2) ∨ False)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h5
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h15 =>
            -- False on the left can always be used.
            apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h5
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139966076582143131906778555327 : (((False ∨ ((True → (((False → p4) ∨ (((p3 ∧ p3) ∧ False) → (p2 → (p2 ∧ p5)))) ∧ False)) ∧ p2)) ∧ (p1 ∧ p1)) → ((False ∧ p4) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193441522322204086289146876653 : (((p1 → p3) ∧ (False ∨ (((p1 → p1) ∨ p5) → p5))) → ((p1 → p3) → (p4 ∨ ((p1 → False) → (p5 ∨ ((p4 → (p3 → p5)) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 → p1) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48400813834058874409272178820 : (((p1 → ((False ∨ ((False ∧ (p4 ∨ p3)) ∨ ((True ∨ p4) ∧ ((p1 → (p3 ∨ p1)) ∨ ((p5 → False) → p2))))) → p1)) → (True ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_450784292864198105446402291761 : (((((p3 ∧ (False ∧ (p3 → (((p2 → (False ∧ p5)) → (((p2 ∧ True) ∨ p3) ∧ p5)) ∨ p3)))) ∧ False) ∨ ((False → (p1 ∧ p1)) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251222599393242092441191676662 : ((p2 → p1) ∨ (p1 → (((p2 ∧ p1) ∨ False) ∨ ((True → p4) ∨ ((((p1 ∨ (p4 → (p4 → p4))) → p3) ∧ p5) → ((True ∨ p5) → p1)))))) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800439267121517371741164433788 : (((p2 → ((True → (False ∧ ((((p2 ∨ (True ∧ (((True → (p3 ∧ ((p2 ∧ False) → p5))) ∨ True) ∨ p1))) → p2) → False) ∧ p4))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314910915862476234315476733486 : (p3 ∨ (((((((False ∨ p1) ∧ p2) ∨ p1) ∧ p3) ∨ p1) ∧ p4) ∨ (True ∨ ((((p2 → p4) ∨ ((True → p3) ∨ (p2 ∧ p3))) ∨ p4) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705890503729997793509122878701 : ((((((p3 ∧ p2) ∨ p2) ∨ ((p3 ∨ p2) ∧ True)) ∧ (p2 ∨ (p1 → ((p2 ∧ (p2 → (p5 → (p1 ∨ (True ∨ (p3 ∨ p5)))))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134329693666010375132838221799 : (((p2 ∧ (p4 → (((((True → p1) → ((((False ∨ p2) ∧ p5) ∨ p2) ∨ p4)) ∧ (p1 ∧ p5)) ∧ p1) ∨ True))) ∨ True) ∨ ((p4 → p5) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745484380600502659951955501185 : ((((True ∨ True) → ((((p3 ∧ p1) → p4) ∧ (p4 ∧ ((False ∨ p3) ∨ (True ∧ p4)))) ∧ (p5 ∨ ((p1 ∨ (p2 ∧ (p3 ∧ p3))) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54725607907654794417002348202 : ((((p4 ∧ (p4 ∨ p5)) ∧ ((True → False) ∧ p5)) → (p3 ∨ (((True ∧ (p1 ∨ False)) → (((p5 ∨ p4) → (p5 ∨ p1)) ∧ p5)) → False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42760479773018058711810970159 : (((True → (p4 → (((True ∨ (p4 → p4)) → ((p2 ∨ p5) ∧ True)) ∨ ((p4 → (False ∧ p4)) ∨ ((p4 ∧ p2) ∧ (p1 ∨ p1)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115125865525396137174293945919 : ((((p1 ∨ (((p1 → p5) ∧ p4) → True)) → (True ∧ (p3 ∧ p2))) → (p5 → ((((True ∨ p1) → p2) ∧ (p5 → p2)) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115145679592369630185377431530 : (((p5 ∧ (((True ∧ (p2 ∧ p5)) ∨ (False → (p1 ∧ p3))) ∧ p3)) → (p3 ∧ (((False ∨ (p2 ∧ False)) ∨ p1) ∧ (p3 ∧ p4)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354803395380071012145471243584 : (p5 → (((p5 ∨ ((p2 ∨ p3) ∨ p3)) ∧ ((p3 ∨ p2) ∧ (p4 ∧ (p1 ∨ (((p4 ∧ (True → p2)) ∧ (True → (p5 → False))) → p3))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630380430043071844486135770502 : (((((p3 ∧ (((p3 ∨ (p4 ∧ True)) ∨ p3) ∨ ((True ∧ p1) → ((False → (((p4 → p3) ∨ p5) → p5)) ∨ (p3 ∧ p2))))) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299149587394225211233462339401 : (False ∨ (((False ∧ ((((p3 → p3) ∨ (p4 ∧ p5)) ∧ ((True ∧ p5) ∧ (p4 ∧ p4))) → (p2 → (p3 ∨ (p5 ∧ (p2 ∧ p3)))))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175274777854946911427852632402 : ((p2 ∨ (p1 → ((p2 → (p2 → ((p5 ∧ ((p5 ∨ p1) → p3)) ∧ p2))) → False))) → ((p5 ∨ (p5 ∧ ((p2 → (False ∨ p4)) → p1))) ∨ True)) := by
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
theorem thm_5_vars_64985481283304378520998467885 : ((p2 ∨ ((p2 ∨ (p2 → (False ∧ p3))) → ((((False → (False ∧ (p1 ∨ (p2 → (p3 ∧ True))))) → False) ∧ (p1 ∧ False)) ∨ (p4 ∨ True)))) ∨ p5) := by
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
theorem thm_5_vars_307330090644468948994716155836 : (p1 ∨ (p3 ∨ ((((False ∨ p3) ∧ p1) ∨ p3) ∨ (False → ((p4 → ((((False ∧ True) → True) ∧ p2) → p3)) → (True ∧ (p1 → (p4 ∧ p3)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307459686354624358054799058965 : (p1 ∨ (p5 ∨ ((False → False) → ((((p5 → (p1 ∧ True)) ∨ (p5 → p2)) ∨ ((p4 ∨ p2) → (p3 → (False → (p3 ∨ (p3 ∨ p2)))))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696763700695768309420669651659 : (((((((True → (False → True)) ∧ p4) → (p4 ∨ (False ∨ p5))) → p5) ∧ ((p3 ∨ True) ∧ (((False ∧ p2) ∧ False) ∧ (p4 ∨ (False ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37440898347428107714524224442 : ((((((p3 → p1) ∨ (((p1 ∧ (True ∧ (p4 ∨ p4))) ∧ (p5 ∧ (p3 ∨ p4))) → p2)) → (p1 → ((p3 ∧ p5) ∧ True))) ∨ p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563586274437109188109634114185 : (((p5 ∨ ((p1 ∨ p3) → ((p4 ∧ (p5 ∧ (((p1 → p3) ∧ ((((p1 ∨ p4) ∧ p1) ∧ False) ∨ True)) ∧ p5))) ∨ (True ∨ (p3 ∨ p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248214969222825330098352967379 : ((p2 ∨ p1) ∨ (((p4 → p2) ∨ ((p4 → ((p2 ∨ True) → (p5 ∨ ((p4 → (p3 ∧ False)) ∨ p5)))) ∨ p4)) ∨ ((p5 ∧ (p3 ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231953093796565187042858262366 : (((p1 ∨ p1) → p4) → ((False ∧ (p4 ∨ (p1 ∧ ((p5 ∧ (False ∨ (True → p3))) ∨ ((p1 ∨ (p1 → ((p3 → False) → p1))) ∨ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185583934089301670161042226018 : ((p5 ∨ (((p2 → p4) ∨ (False → (p5 → (p5 ∧ p4)))) → p2)) ∨ (((True ∨ p3) ∨ (p2 ∧ (((False ∨ (p4 ∨ p3)) → True) ∨ p4))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46060964284221290310470945808 : ((((((p3 ∨ (p2 → (((p2 ∨ p4) ∧ p3) ∨ (False ∨ p3)))) ∧ ((p4 ∧ (p4 ∧ p1)) ∧ (p5 ∧ False))) ∨ p1) ∨ p2) ∧ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134211428180171389492324234651 : ((((p3 ∧ ((p4 ∧ ((False ∧ p4) → False)) ∧ True)) ∨ (((((p5 ∨ p3) ∨ p2) ∨ (p1 ∧ p3)) ∧ p2) ∧ p2)) ∨ p5) ∨ ((False → False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1505612488777028062847295994 : (((((False → p3) ∨ ((p5 ∧ ((False ∧ (p1 ∨ p2)) → False)) → (p4 ∨ p4))) → p2) → (p4 ∧ ((True ∨ p3) ∨ p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116048995741598850645270813430 : (((p1 → (p3 ∨ (p2 ∨ p2))) → (p3 ∨ ((((p2 ∧ ((((p1 ∨ p5) ∨ True) → True) → p5)) ∨ False) ∧ (p5 ∨ p4)) ∨ True))) ∨ (p5 ∨ p4)) := by
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
theorem thm_5_vars_670281749718531219617181902040 : (((((True → (p2 → (p5 → p2))) → (((((False ∨ True) ∨ p1) ∧ (p3 ∨ (p4 → p5))) ∨ (True ∨ p2)) ∨ False)) ∨ ((True → p1) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_660579836516036115030028748057 : ((((((p4 → ((True ∧ ((p1 → p3) ∨ (p2 ∧ p5))) ∧ (((True → p4) ∨ ((p4 ∨ p1) → p3)) ∧ True))) → False) → p3) → (p2 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305788917689633050309470969959 : (p1 ∨ ((p5 → ((False ∨ ((p4 ∧ False) ∧ p5)) ∧ p4)) ∨ (False → (((p2 ∨ ((p4 ∨ p3) ∨ (p3 → (p2 ∨ p2)))) ∨ (False ∧ p3)) → p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h1
        case inr h8 =>
          -- False on the left can always be used.
          apply False.elim h1
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h1
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44520229454891763892231276147 : (((((p1 ∨ p3) → ((p1 ∧ False) ∨ ((p3 ∧ p1) ∧ p1))) ∨ (((((p4 ∨ p1) ∨ p2) ∧ p3) → (p1 → False)) ∧ (True → p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340951658159680970133991088389 : (p2 → ((((p3 ∨ p4) ∨ False) ∨ (True ∧ (((p1 ∨ ((((p1 ∨ ((p5 ∨ p2) ∨ p4)) ∧ False) ∧ (p5 ∨ False)) → p1)) ∧ p5) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714683096334063950899573763562 : (((((p3 ∨ p3) → ((p5 ∨ p1) → p3)) → (((((p5 ∨ p1) ∨ p4) ∨ p2) → p2) ∨ ((p3 ∨ p5) → (p2 ∧ (p5 ∨ (p5 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657987872446802738717330682648 : ((((p2 ∧ (((((p4 ∨ (p2 → ((False → p4) ∧ False))) ∨ True) ∨ (p5 ∧ p1)) ∧ (p5 → True)) ∧ (p1 ∧ (p2 ∧ p1)))) ∨ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327804353812614362790605746419 : (True → (((((((p4 ∨ p2) ∨ (p2 ∧ p5)) → p4) → False) ∨ ((p3 → p2) ∨ ((((p2 ∨ p3) ∧ p4) ∧ p5) ∧ p1))) ∨ p2) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327011962828639750216242793343 : (True → (((((p5 ∧ True) ∧ False) → (p3 → (p2 ∧ (p3 ∨ (((p3 ∧ False) ∨ p4) ∧ p1))))) → (False ∨ (p2 ∧ ((p1 ∨ False) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117472158226339857042383808520 : ((p1 ∧ (p3 ∧ (p2 ∨ (((p4 ∧ p5) → (p4 → (p4 → p1))) → (((((p2 → (p1 ∨ False)) ∧ p1) ∧ p4) → False) → p1))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198290376213550989084776828239 : ((p1 ∧ ((((p4 → False) → p4) ∨ p3) ∧ p2)) ∨ (True ∧ (p4 ∨ ((((False → p5) ∧ p2) → p2) ∨ ((((False ∨ p5) → p1) ∨ True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166544067462346583411591807039 : ((p5 ∨ (((p3 ∨ True) ∨ ((p3 ∧ (p1 → (p4 ∧ p1))) ∨ (False ∧ (p4 ∧ p5)))) → False)) ∨ (p3 ∨ (True → ((True → (False → p1)) ∨ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64136040825961495171522656642 : ((False ∨ ((p5 → ((p5 ∧ p3) ∧ True)) → (((p3 ∨ ((p5 → p5) ∧ ((False → p3) → (((p1 ∧ True) ∧ p4) → False)))) → p4) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113381367468323623155483163951 : (((p4 ∨ (p1 ∧ ((((p1 ∧ p4) ∧ ((False ∨ (p1 ∧ True)) → ((False ∧ (p3 → True)) ∧ p2))) ∨ False) ∧ p2))) ∧ (True → p3)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68548382411357836024798645280 : ((p3 → (p4 → (((p3 ∨ p2) ∨ ((((p2 ∧ p3) ∨ ((p4 ∨ p5) → p4)) ∨ p1) ∧ p3)) → (p5 ∨ (p1 ∨ (p3 → (False → True))))))) ∨ p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664916712631189613684579072856 : ((((p3 → ((p5 ∨ ((p2 → True) ∨ ((p2 → (((p1 ∨ (p3 ∨ (p2 → p2))) → p3) ∧ p1)) ∧ (p1 → p2)))) ∨ True)) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66153539592897115954241718703 : ((p5 ∨ (((True ∧ p1) ∧ ((True ∧ (((((p3 ∨ (p2 ∧ p3)) ∨ p4) ∧ p1) ∨ (p1 ∨ p3)) ∧ p5)) ∨ (p2 → p2))) → (False ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174652466525285806575716933115 : ((((True → p5) ∨ p3) ∧ ((p1 ∨ p4) ∨ (True ∧ ((False → (p1 ∧ p4)) ∨ True)))) → (p2 → ((((p5 → True) → (p3 ∨ p3)) ∧ p4) ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137387327812723171536702283399 : ((p3 ∧ ((True → (False → True)) → (p5 ∧ (((p1 ∨ (((p3 ∨ p2) ∨ p4) ∧ ((p3 → p4) ∨ p2))) ∧ False) ∨ p5)))) ∨ ((False ∧ p4) → p2)) := by
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
theorem thm_5_vars_94774052670454892078291164825 : ((p3 ∧ (((p2 ∨ ((True → True) ∨ p2)) → p5) ∧ (p5 ∧ (p3 ∨ ((False ∨ p3) ∧ ((((p1 → p2) ∨ p5) ∨ True) → (p4 ∨ p5))))))) → p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726618710028536345733017233908 : (((((p1 ∧ True) → p4) ∨ ((((False ∨ True) ∨ p2) ∧ ((False → p3) ∨ (p4 → p2))) → (True ∧ (((False ∨ (p4 ∨ p1)) → False) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
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
    cases h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700368250879750326545761755519 : ((((p4 ∧ ((((False → (p5 ∨ False)) ∧ (p5 ∨ p4)) ∧ p4) → p5)) → (((True ∧ (((p1 ∧ p1) ∨ p4) ∨ True)) → (False ∧ p3)) ∨ p4)) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56900286222805921155370364583 : (((p4 ∧ (p3 ∧ False)) ∧ ((False ∧ p5) ∨ (((p5 ∧ (((True ∨ p1) ∧ p3) → p1)) → (p2 → p2)) ∨ ((False ∨ (p3 ∧ p1)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190276798567521076898447160827 : ((((p4 ∧ (p5 ∧ (p2 ∨ (False ∧ p4)))) ∨ p5) ∨ p4) ∨ (True → ((p4 ∧ p3) → (False ∨ (((True ∨ (p2 → p2)) ∨ (p1 ∨ p5)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324735686688334874449576242538 : (p5 ∨ ((p1 ∧ (p3 ∨ p5)) → ((((p2 ∨ (p2 ∧ False)) ∧ ((p4 ∨ p1) ∧ p5)) ∧ (((p3 ∨ (False → p2)) ∨ True) → (p3 ∧ False))) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : ((p3 ∨ (False → p2)) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h23 : ((p3 ∨ (False → p2)) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317716976881773195131077696086 : (p4 ∨ (((((p5 → (p2 ∧ ((((False ∧ p2) ∧ p4) → p4) ∧ p5))) ∨ ((False → (p3 → True)) ∧ p5)) ∨ (True ∨ p5)) → (p4 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177781933244933711772985264951 : (((p4 ∧ ((False ∨ (p1 → (((p3 ∧ True) ∨ True) ∧ p2))) ∨ p1)) ∧ p3) ∨ (True ∨ ((((p2 ∧ p4) ∨ p1) → (p4 → p1)) → (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38318352414695814258642361097 : (((((True ∧ p3) → ((False ∧ (p4 ∧ (((False → False) ∧ True) ∨ ((p2 ∨ p1) ∧ p3)))) ∨ p1)) → ((p1 → p5) → (p4 ∧ p1))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157002721736325774468169618628 : ((((p3 ∨ ((p3 → p4) ∧ p4)) → ((p2 → ((p1 ∧ (False → p1)) ∨ (p2 ∨ p4))) ∧ p5)) ∨ p1) ∨ (((False → p4) ∧ False) → (p3 ∧ p5))) := by
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
theorem thm_5_vars_784576340150210547853285031303 : (((p3 ∨ (p1 ∨ ((True ∧ ((p3 ∧ p3) → (p1 ∨ (((p4 ∨ p5) ∨ (False ∧ p5)) → (True → False))))) ∧ ((p5 ∨ (True ∧ p4)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660623706726106938010286700120 : ((((((p2 → (((False → True) ∨ ((p2 ∨ (p1 ∧ (((True ∨ False) ∨ p4) ∧ p3))) ∨ p1)) ∨ p4)) → (False ∨ p1)) → p3) → (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209287678207761005918913528635 : ((True → ((True ∧ p4) ∧ (p4 ∧ False))) → (((((p2 ∧ (p3 ∨ p4)) ∧ (((p2 ∧ False) ∨ (p3 → p1)) ∧ True)) ∨ False) ∨ True) → (p2 ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h6.left
        let h11 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h6.left
        let h18 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h26 := h1 h25
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78533227968464427374147527152 : (((((False ∨ ((p3 ∧ False) → True)) ∨ (True ∨ ((False ∧ ((p4 ∨ True) ∧ (p1 ∨ True))) ∨ (p4 ∧ (p2 ∧ p3))))) → p3) ∧ (p4 → p2)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((p3 ∧ False) → True)) ∨ (True ∨ ((False ∧ ((p4 ∨ True) ∧ (p1 ∨ True))) ∨ (p4 ∧ (p2 ∧ p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137810814134281664200424929513 : ((p3 ∨ (((((p2 ∨ (p3 ∧ (p2 ∨ (True ∨ p1)))) ∨ p3) ∧ (p4 → (p2 → True))) → ((False → p3) ∧ p2)) ∧ False)) ∨ (p5 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172805012133464044427320855443 : ((True ∧ (((p2 ∧ ((True → ((p3 → p5) ∧ p2)) → (p3 → False))) ∨ p5) ∧ p5)) ∨ (False ∨ ((p2 → (True → True)) ∨ (p2 ∧ (p2 ∨ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790297416725985418975152674008 : (((p5 ∨ (p2 ∧ (((True → (True ∧ False)) ∨ (False ∧ p4)) → ((((((p4 → p3) → p2) → (p4 → p5)) → p5) ∨ True) ∧ (p4 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150055897612743827320089251492 : ((True → ((((((p4 ∧ False) ∨ p4) ∧ (p3 ∨ (False ∧ p5))) → (p4 ∧ (False ∧ p4))) ∨ (p2 ∨ p3)) → p3)) ∨ (p1 → (True ∨ (p2 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53776677630464334534950845842 : (((((p3 ∨ (p2 ∨ p5)) ∧ (p1 ∨ (True ∧ p1))) ∨ p3) ∨ (p2 → (p5 ∧ ((((False → True) ∨ p2) ∧ ((p4 ∨ p5) ∧ p1)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157143358758581991201051880562 : ((((((((p5 ∨ ((False ∧ False) ∧ (p1 → p1))) ∧ p3) ∧ False) → (True ∨ p5)) ∨ True) ∨ p1) → p3) ∨ (True ∨ ((False → (p4 ∨ p3)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207987067384669393178436713399 : ((((p3 ∧ p1) ∨ p4) ∨ (p3 ∨ p5)) → ((True → ((p4 ∧ False) ∧ True)) → ((((p5 → ((p4 ∧ p3) → p1)) → p1) → p2) → (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355600279698626631979917111083 : (p5 → ((((True ∨ p1) ∨ True) → (p5 ∧ ((p2 ∨ (p3 → ((True ∨ True) ∧ (((p3 → p3) → (False ∨ p5)) ∧ p3)))) ∨ p3))) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300387256981604911087321158123 : (False ∨ ((((((True ∨ p5) → False) ∧ p2) ∨ p1) ∨ ((((((p2 ∨ False) → True) → (p2 → p4)) ∧ p3) ∨ p3) → p3)) ∨ ((p4 ∨ p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618619165520393118685726962462 : (((((p4 → (p4 → (True → False))) → ((p2 ∧ False) ∨ (p2 ∧ ((((False ∨ p3) ∧ p1) → (p5 ∧ (True ∨ p3))) → (True → p1))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351629175432685419682645835650 : (p4 → ((((p5 ∧ (p1 ∨ ((True → p2) ∨ ((p4 ∧ p3) ∧ (p4 ∨ p5))))) ∨ True) → p1) ∨ ((p5 ∧ (True ∨ ((False → p2) → p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327065240502264457143393516528 : (True → (((True → (p3 ∨ (p4 ∧ p1))) ∧ (p3 → ((((((p5 ∧ p3) ∨ False) ∧ ((p1 ∨ p4) ∧ (False ∨ p1))) → p4) ∨ False) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177963885179898238724373150942 : ((((p4 → False) ∨ ((p2 ∧ p1) ∨ ((p2 ∨ p1) → (p5 → p2)))) ∨ p1) ∨ ((False → (True ∨ (False ∧ (False → (p4 ∧ p4))))) ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253745745385272826120972317715 : ((p1 ∧ p1) → ((((True ∨ True) ∨ ((p3 ∧ p3) ∨ p3)) → (p1 → (p4 ∧ False))) ∨ ((False ∨ ((p3 ∨ p1) ∧ p1)) ∨ ((False → p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216301376942478598152054030233 : ((p2 → ((False ∨ p2) → p5)) ∨ ((p1 ∧ (p4 ∧ False)) ∨ ((True ∧ ((((False → (p2 → False)) → False) ∧ (True ∨ (p2 → p4))) ∧ p4)) → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (False → (p2 → False)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h9
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : (False → (p2 → False)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h14
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66367415913113308364624001385 : ((p5 ∨ (p1 ∨ ((False ∧ (p2 → False)) ∧ (((p4 ∧ (p1 ∧ ((True ∧ True) ∨ p5))) ∧ (p1 ∧ p1)) ∨ (False ∧ (False ∨ (True → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41692416551459725003338542151 : (((((p4 ∨ (p5 ∨ (p1 ∨ False))) ∧ p3) → ((((p5 → False) → p1) ∨ (p4 → False)) ∨ ((((p5 ∨ p2) ∧ p2) ∧ p3) → False))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234009758281542596678146491068 : ((p5 ∨ (p3 ∨ p2)) → ((p2 ∧ (p3 ∧ (False → ((((p2 ∧ p4) ∧ (p4 ∨ False)) ∨ p1) ∧ (p1 → p1))))) ∨ (p5 ∨ (False → (True ∨ True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199532247505896317532769847772 : ((((((p1 ∨ p5) ∨ p1) → True) ∧ True) → True) → (p2 ∨ (((False → p1) → p5) → (p1 → ((p2 ∧ (p3 → (False ∨ (p5 ∧ p4)))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674635659775329746569744671436 : ((((False → (p3 → ((p3 ∧ (False → (True → True))) ∧ (((p3 ∨ (p5 ∨ p5)) ∨ (p4 ∧ (p5 ∨ p1))) ∨ p3)))) → (p2 ∧ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684372063543512616615033619775 : ((((((False ∧ p2) ∧ (True ∧ (p3 ∧ (p1 → (False → p2))))) ∨ ((p5 → (p4 ∨ p3)) ∨ p5)) ∨ ((True → p1) → (p4 → (False → True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769463457993255982614984468478 : (((p5 ∧ (p2 ∧ ((((p5 → p1) ∧ ((p3 ∧ p4) ∨ (p4 ∧ (p4 ∧ p2)))) ∧ p4) ∧ (p5 → (((True → p5) ∧ (p4 ∧ False)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179997858683208258869021853644 : ((((p3 ∨ (False → False)) → ((p3 ∧ (p1 ∨ (p5 ∨ p3))) ∨ True)) ∨ p5) → (((p4 ∨ p5) ∧ ((p1 → p5) ∨ ((p5 ∨ p4) ∧ p3))) ∨ True)) := by
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
theorem thm_5_vars_57402885462822540042166911685 : (((False ∨ (p1 → p5)) ∨ (((p2 ∨ (p5 → (((p5 → True) ∧ p2) ∧ (True ∨ (p1 → p5))))) → ((p4 ∨ (p1 ∨ True)) → p5)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308424746042902274368665644541 : (p2 ∨ ((((p1 ∧ ((p4 → (p5 ∧ (p2 → ((False ∧ False) ∨ p4)))) ∨ p3)) ∨ (False ∨ ((False → (p4 → True)) ∨ (p5 → p4)))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148585579729173020115740413509 : ((((False ∧ (p4 ∨ ((p5 → p1) ∨ p4))) ∧ (True ∧ p2)) ∨ (p3 ∨ (((p3 ∧ (p2 ∧ p1)) → p3) ∧ p5))) ∨ (p5 ∨ ((False ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259660894839689072561525458744 : ((p1 → False) → (p4 ∨ ((p3 → True) → (((p1 → False) ∨ p4) ∧ (((((False ∨ False) ∧ p3) ∨ (p3 ∧ False)) ∨ p2) → (True ∧ (p4 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



