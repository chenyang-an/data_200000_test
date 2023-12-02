variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158961056070219280601700427101 : ((p2 ∨ (p5 ∨ (((p5 ∧ p3) ∨ p1) ∧ ((p1 ∧ (p3 ∨ (p4 → ((p3 → False) → p4)))) → p3)))) ∨ (p2 → ((p5 → (p2 ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742917373960836962223515116378 : ((((p3 → p4) ∨ (((p5 ∨ p2) → (p2 → (True ∧ (((((True ∧ (p3 ∧ p5)) → p4) ∧ p5) ∧ ((p4 ∨ p5) ∧ True)) ∧ False)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732320808505343252447520641919 : ((((False ∧ p1) ∧ ((((p2 → ((p3 ∧ (p2 ∨ (p5 ∧ p5))) ∨ False)) ∧ (p5 ∧ True)) → (((p4 ∧ p1) ∨ p2) ∧ (p3 → p1))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58744740364064725502469658602 : (((p3 → p5) ∧ (((p5 → (False ∧ (False → ((p2 ∨ True) ∧ ((p3 ∨ p4) ∧ True))))) ∨ (p4 ∧ False)) ∧ (p1 ∧ ((p2 → p2) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118868963500356574234013604881 : ((True → (((p1 ∧ p3) ∨ p2) ∨ (((((p4 ∨ True) ∧ (p1 → (True ∨ p3))) → (p2 ∧ (p3 ∧ True))) ∧ True) ∨ (p5 → False)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112306451383619804711103966226 : (((p2 → (((False ∧ (p4 ∧ ((p2 ∧ (p4 ∧ False)) ∧ ((p4 ∧ p3) ∧ p3)))) ∨ (((False → p4) → True) ∧ p2)) ∨ p3)) ∨ False) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118248689201365830730308435365 : ((p1 ∨ (((((((p5 ∨ p4) ∨ (p5 ∨ p5)) ∧ True) → ((True ∧ (False ∧ p3)) ∧ p1)) ∨ p5) ∨ p4) ∧ (p5 → (p5 ∨ p4)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647368943191831632793923263824 : ((((p4 → (((p3 → ((p3 → p5) ∧ p5)) → (False ∧ False)) ∨ (p1 → ((p2 ∨ p3) ∧ (((p2 ∨ p1) → (p2 → p2)) ∧ p4))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655873372590932653135009875333 : ((((((p1 → p3) ∨ (True ∧ ((p3 ∧ p3) ∧ (p2 ∨ (((p1 ∧ False) ∨ (p1 → p4)) → p3))))) → ((True ∨ p3) ∧ p5)) ∨ (p5 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_116143537125605636069927385097 : (((p5 ∧ (p4 → p3)) ∧ (True → ((False → ((p3 ∧ p3) ∧ (True → ((True ∨ False) ∨ True)))) → (p5 ∨ (p2 ∧ (p4 → p4)))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313070700552767101240943366342 : (p3 ∨ (((((p2 ∨ (((p5 → p3) ∨ p3) ∨ ((p4 → p4) → (p3 → ((p4 ∨ (True ∨ p3)) ∧ p4))))) → p5) → False) ∧ (p2 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136495968394311046334667972699 : ((((p3 ∨ p3) → p1) ∧ ((((((False → p5) → (True ∨ p5)) → p4) ∧ p1) → p2) ∨ (((p5 → p4) → p2) ∧ p3))) ∨ (p2 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138381602086795570478762970274 : ((p4 → ((p3 ∧ p5) ∨ (p3 ∨ (((False → p3) ∧ ((p3 ∨ (False ∨ (p1 ∨ p5))) ∨ True)) ∨ ((True ∧ True) → False))))) ∨ ((True ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319883426943177141114533968222 : (p4 ∨ ((p5 ∧ ((p1 ∨ p4) ∨ False)) ∨ (p4 → ((((p4 ∨ True) ∧ p1) ∧ p3) → (p1 → ((p4 ∨ True) → (((p4 ∨ True) ∨ p4) ∧ p3))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h2.left
    let h14 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h2.left
    let h21 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h2.left
    let h28 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h32 =>
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90951292617842879309397082701 : (((True → p5) ∧ (p4 ∨ ((((p5 → False) ∧ (p5 ∧ (p3 ∧ (((True ∧ False) → True) ∨ (((p4 → p3) ∨ p3) ∨ False))))) → p2) → p4))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p5 → False) ∧ (p5 ∧ (p3 ∧ (((True ∧ False) → True) ∨ (((p4 → p3) ∨ p3) ∨ False))))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h16 := h8 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h20 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h21 := h8 h20
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h23 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h24 := h8 h23
            -- False on the left can always be used.
            apply False.elim h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h26 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123335500173526751520048745666 : ((((p2 → ((p4 ∧ p5) → p3)) ∨ (((p2 ∨ (p2 → (p5 ∨ True))) → p5) ∧ (p3 ∧ False))) ∨ (p2 ∨ (p5 ∨ (True ∨ p5)))) → (p1 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183786719572490447248300863412 : ((((p3 ∨ ((p5 ∧ (p2 → (p5 ∨ p5))) → p2)) ∧ True) ∧ p4) ∨ (p5 ∨ ((p4 → p4) ∧ ((True → ((p5 ∨ True) ∧ p3)) ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642881270125463436017101540165 : ((((p2 ∧ (((((p3 → True) ∨ p5) ∨ (False ∨ p3)) ∧ ((((p5 ∨ ((False → p4) ∧ p4)) → (p3 ∨ p4)) ∧ p1) ∧ p4)) → p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180255090231384769959083429003 : (((p2 ∨ ((p2 → (p3 ∨ (p1 ∨ True))) ∨ (False ∨ (p4 → p5)))) → p4) → (((p5 → p5) ∧ (True → True)) ∧ (p1 ∨ ((p5 → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ ((p2 → (p3 ∨ (p1 ∨ True))) ∨ (False ∨ (p4 → p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149833958555863119993337214519 : ((p1 ∨ ((p1 ∧ (False ∧ (((True ∧ p2) ∧ (p4 → p1)) → p5))) ∨ ((p1 ∨ (True → False)) ∨ (p2 → True)))) ∨ (False ∨ ((p2 ∨ p3) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212566288142384150339971136048 : ((p5 ∨ ((p2 ∨ p4) → True)) ∧ ((True → p1) → (((p3 ∨ (p2 → p3)) → (p2 ∧ (False ∨ True))) ∨ (((True ∧ (p4 → p2)) → True) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244078537816679848057327101633 : ((True ∧ p3) ∨ ((((((((True ∧ p4) ∨ True) → p2) → True) → p4) ∨ ((((True → False) → (True → p2)) ∨ False) → False)) ∧ False) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40204879399116528315431344713 : (((((p4 → True) ∧ (p2 → ((((False ∧ ((p1 ∧ p2) ∧ ((p2 ∨ (p3 ∧ p1)) → p2))) ∧ False) → False) → (p2 ∧ p1)))) ∧ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301443777032267537827448575871 : (False ∨ ((p4 ∨ (p3 ∨ (p2 → p4))) → (((((p1 ∨ p2) ∨ p4) ∨ p1) ∨ (p3 → ((True ∨ p5) ∨ ((p1 → p3) → p4)))) ∨ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323519750495006398526205119940 : (p5 ∨ ((p5 ∧ ((((((True ∨ True) → p2) ∧ p1) → (True ∧ ((False ∧ ((p2 → p2) → p1)) → p2))) → p4) ∧ p1)) ∨ ((p5 ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337946398778334449011239108848 : (p1 → (((((p3 ∨ ((p3 ∧ p1) ∨ p1)) ∧ p4) ∨ p2) ∧ (False ∨ p5)) ∨ (((p2 ∧ (p4 ∧ ((p4 ∨ p4) → True))) → (p2 ∧ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40635359284068486605196406020 : ((((((((True ∧ False) → ((p1 ∧ p2) ∨ ((p4 ∨ (p4 ∨ p4)) ∨ True))) ∨ p1) → ((True ∧ True) ∧ (p3 → p4))) → p2) → p5) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45499434752394629320876682414 : (((False ∨ (p3 → ((((True ∧ (((p2 → True) ∧ p4) ∨ False)) ∧ ((True ∨ (p5 → p2)) ∨ (p3 ∧ True))) → p2) ∨ (p4 ∧ p3)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178695188036296460417772248514 : ((((p5 → (p1 ∨ p2)) → p2) ∨ ((p1 ∨ (False ∧ p3)) ∨ (False → p2))) ∨ ((p5 → p3) ∧ ((p1 → p3) ∧ ((p3 ∨ p5) ∧ (p5 ∧ p1))))) := by
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
theorem thm_5_vars_51553642455555019284494125543 : (((p5 ∧ (((True ∨ ((p3 → ((False ∨ (True ∨ p2)) → p4)) ∧ (p4 ∨ p5))) ∧ True) ∧ p3)) → ((False ∧ False) ∨ (False ∨ (p5 → p5)))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328720930478760351881468594233 : (True → (((((p2 ∨ (p2 ∨ p2)) → ((p2 ∨ False) ∧ p5)) ∨ p4) ∧ p3) → ((p2 ∧ (p2 → (p3 → False))) ∨ (p3 ∨ (True ∧ (p5 ∧ p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148612909132539692706414407812 : ((((((p5 → ((p3 → p5) ∧ False)) → p1) ∨ True) → p5) → (p2 ∨ (True ∧ (p5 → (p1 ∧ (True ∨ p1)))))) ∨ ((True → p3) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754125806592029891419455812673 : (((False ∧ ((p2 → (p5 ∧ False)) ∧ (((p1 ∧ (((p3 → False) ∧ p5) ∨ p2)) ∧ ((p5 → (True ∨ (p5 ∨ (True ∧ p5)))) → p1)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303766828855087047030761106627 : (p1 ∨ ((((p2 ∧ (p4 ∨ (p5 → p1))) → ((((((p5 ∨ True) → (p4 ∨ (p1 → (True ∧ p2)))) ∧ p1) → p5) → p5) ∧ p1)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961230238543813309965971016072 : ((((p1 ∨ p5) ∧ ((p1 → (((False ∧ (p3 ∧ p5)) → p1) ∨ (p1 ∧ p5))) → ((p4 → (p5 → (p1 ∧ (False ∨ (p3 ∨ p1))))) ∧ p4))) → p4) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (((False ∧ (p3 ∧ p5)) → p1) ∨ (p1 ∧ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h5
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p1 → (((False ∧ (p3 ∧ p5)) → p1) ∨ (p1 ∧ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188094765770205659671244451279 : ((((((p2 → (p5 ∧ p4)) → False) ∨ p1) ∧ p2) ∨ True) ∧ ((False ∨ (((p3 ∧ p5) ∧ p4) ∧ (True ∨ ((p1 ∧ (p5 ∨ False)) → p1)))) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86599411207641027237001959535 : ((((p2 → ((False ∧ True) → (True → p5))) → False) ∧ (p1 ∨ (((p3 → p4) ∨ p4) ∨ ((p1 ∧ False) ∨ ((True → (p2 → p5)) ∨ True))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → ((False ∧ True) → (True → p5))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h5
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (p2 → ((False ∧ True) → (True → p5))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- False on the left can always be used.
          apply False.elim h19
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h15
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h23 : (p2 → ((False ∧ True) → (True → p5))) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- Implications on the right can always be decomposed.
          intro h26
          -- Conjunctions on the left can always be decomposed.
          let h27 := h25.left
          let h28 := h25.right
          -- False on the left can always be used.
          apply False.elim h27
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h29 := h2 h23
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h36 : (p2 → ((False ∧ True) → (True → p5))) := by
            -- Implications on the right can always be decomposed.
            intro h37
            -- Implications on the right can always be decomposed.
            intro h38
            -- Implications on the right can always be decomposed.
            intro h39
            -- Conjunctions on the left can always be decomposed.
            let h40 := h38.left
            let h41 := h38.right
            -- False on the left can always be used.
            apply False.elim h40
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h42 := h2 h36
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h44 : (p2 → ((False ∧ True) → (True → p5))) := by
            -- Implications on the right can always be decomposed.
            intro h45
            -- Implications on the right can always be decomposed.
            intro h46
            -- Implications on the right can always be decomposed.
            intro h47
            -- Conjunctions on the left can always be decomposed.
            let h48 := h46.left
            let h49 := h46.right
            -- False on the left can always be used.
            apply False.elim h48
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h50 := h2 h44
          -- False on the left can always be used.
          apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259250531056786795104447287979 : ((False → p1) → ((((p3 ∧ (p3 ∧ ((p1 → (p3 ∧ p5)) ∨ (p4 ∨ (p5 ∧ p2))))) ∨ p1) ∧ (p1 → ((True → False) ∨ (p4 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66341688739979156475498755375 : ((p5 ∨ (p4 ∧ (((p4 ∨ ((p2 ∨ (((p5 ∨ (False ∨ (p3 ∨ p1))) → p4) ∨ True)) ∨ (p2 ∨ (p5 ∨ True)))) ∧ (p5 ∨ p2)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616929998739389643070351648591 : (((((p1 ∧ ((True → (False ∧ (p5 ∧ p2))) ∨ (True → p4))) → ((((p2 ∨ ((False ∨ p2) ∧ p2)) ∧ (p3 ∨ p4)) ∧ p3) → p2)) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h1.left
        let h30 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46068243526003922702502124878 : (((((((((((False ∧ False) ∨ False) ∧ True) → True) ∨ True) ∧ p5) ∨ (p1 → ((p2 → True) ∧ (p3 ∧ p2)))) → p5) ∨ p3) ∧ (p4 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330913715906155482379127727448 : (True → (p4 → (((p4 ∧ (p3 ∧ p3)) ∨ ((((p1 → p5) ∧ (p3 ∨ True)) ∨ (p1 ∨ p3)) ∨ (p1 → ((p3 ∨ p2) → True)))) ∧ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39668141443100157572645859323 : (((p4 ∨ ((((p5 ∨ ((p4 → ((p4 ∧ (True → (((p5 → p5) ∨ p2) ∧ False))) ∧ False)) ∨ (False ∨ p5))) ∧ p2) → p4) ∧ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983444315247234500047347407847 : (((p1 ∧ ((True → (((p1 ∧ p4) → p1) → p5)) ∧ (p3 → ((((p4 ∧ p4) → p2) → ((p2 → (p5 ∧ p2)) → p3)) ∧ (p4 → False))))) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∧ p4) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315061300786226166970124607788 : (p3 ∨ ((False ∨ ((p3 → (p4 ∨ (True → p1))) ∧ p1)) → ((((p5 ∧ p2) ∨ p3) ∨ (True ∧ (p3 ∨ (p5 ∧ (p4 → p2))))) ∨ (False → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776958677915367437244991778787 : (((p1 ∨ (((((p2 ∧ p3) ∨ ((False → (p5 ∨ False)) ∧ (p4 ∨ p2))) ∨ (p4 ∧ ((True → True) ∨ p5))) → (p2 ∨ p1)) ∧ (False → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115704361782581779156021653620 : (((((p2 ∨ p2) ∧ (p2 ∧ p4)) ∧ p4) → ((((p5 ∧ (p3 ∧ (p4 ∧ (p3 ∨ p2)))) ∧ ((p1 ∧ p1) → p3)) ∨ p2) ∨ True)) ∨ (True ∧ p3)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59247344604214643484534956995 : (((p2 ∨ p3) ∨ (p4 ∧ (((p5 → (True ∨ False)) ∨ (p3 → ((True ∧ (p2 → ((p2 → p4) ∧ ((False → p5) → p3)))) ∨ True))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64371827221894717576626825355 : ((p1 ∨ (((p3 ∧ p5) ∨ (((p1 → (False ∨ (p3 ∨ (p3 → (p3 ∧ False))))) ∨ (p5 → ((p5 → p1) ∧ p2))) ∨ (p1 ∧ p4))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161401563401177158339361962428 : ((p1 ∧ ((True ∨ p3) → (False → ((p1 ∨ (True ∧ p2)) → ((p2 ∨ p5) → (False ∧ (p2 ∧ p4))))))) → (p5 → ((False ∧ p2) ∨ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3221201824550678600373554554 : ((False ∨ p2) ∨ (p4 ∨ ((((p1 ∨ ((((p4 → (p2 ∧ p1)) ∨ p3) ∧ (p5 ∨ (p2 ∨ p3))) ∧ p1)) ∨ True) ∨ p1) ∨ (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_631733316543058846596785800103 : ((((((((p2 ∨ p2) ∨ ((p3 ∨ False) → ((p5 → True) → False))) → p1) → ((True ∨ (p1 ∨ True)) ∨ ((p3 ∨ p4) ∨ p5))) → p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339897271192736863022727657183 : (p1 → (True → (p3 → (p3 ∧ (((p1 ∨ (p4 ∨ p5)) ∨ p5) → ((p2 ∨ (p4 ∨ p3)) ∨ (((True → False) → (p5 → (p1 ∧ p4))) ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64068231237321736241177227310 : ((False ∨ ((((True → p5) ∨ ((((p1 ∨ p3) ∧ True) ∧ p3) ∨ (p2 → (p1 ∨ p1)))) ∨ p3) ∨ ((False ∧ (p1 ∧ (p4 ∧ p5))) → p4))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775844361710081664182049414407 : (((False ∨ (True → ((p2 → ((((p1 ∨ ((p3 ∨ ((True ∧ p3) ∧ p2)) ∧ p3)) ∨ False) ∨ True) ∧ (True ∨ p2))) ∧ ((p2 ∨ True) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256597509939653656715251747698 : ((p1 ∨ True) → ((p2 → (((p1 ∧ (p4 ∨ p5)) → False) ∧ (p3 ∨ (p2 → (False → (p2 ∨ p4)))))) ∨ ((False → p2) ∨ (p2 ∧ (False → p1))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103157808329929400304370962639 : ((((p2 ∨ p3) ∨ (True ∧ (((p5 → ((p3 → p3) → p4)) → (((True ∨ p4) ∧ (p2 ∨ p4)) ∨ (True ∨ p2))) ∨ False))) ∨ p4) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214053626977877255355251611801 : ((((p1 → p1) ∧ p3) → p5) ∨ (((((((p5 ∧ False) ∨ True) ∨ False) → True) ∨ False) → ((p1 ∧ p3) ∧ p1)) → ((p1 ∧ (True → p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ False) ∨ True) ∨ False) → True) ∨ False) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730928400094081391003554710461 : ((((True ∨ (p3 ∨ p5)) → ((p2 ∨ ((p2 → False) ∧ ((((p4 ∨ ((p4 ∨ ((p3 ∧ p2) → p5)) ∨ p4)) ∧ p2) ∨ p5) ∧ p3))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327687048152417027719114387799 : (True → ((((((p5 ∨ True) ∨ p5) → True) → (((p1 ∧ (((False ∨ True) ∧ p5) → ((p2 ∨ p1) ∧ True))) → True) → p5)) ∨ True) ∧ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116209849163028580450916149153 : ((((True ∧ p3) ∨ p4) ∨ ((((True ∧ (p1 → p4)) ∧ p3) ∧ p1) ∨ (((p3 → p5) ∧ p3) ∨ (p5 → ((p5 ∨ p3) ∨ p2))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148856470291516893849968930871 : (((p3 ∧ ((True → p1) ∧ p5)) ∧ ((True ∨ (((p1 ∧ p2) ∧ (True ∧ p4)) → ((p2 → p5) ∨ p5))) → p2)) ∨ ((p1 → p1) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38848159902586035362741444344 : (((((p1 ∧ p1) → p2) ∧ (((True ∧ (((p3 ∧ True) ∨ p1) → (p4 ∧ (True ∧ (True ∨ p4))))) → ((p5 ∨ p1) ∧ p5)) ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58987399761941644761110089628 : (((p3 ∧ True) ∨ ((False → ((p3 ∧ p4) ∧ (p4 ∧ p3))) → (p5 ∧ ((p5 ∧ ((p2 ∨ ((p3 ∧ True) ∧ p3)) ∨ True)) ∧ (p4 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111304131734731008908074940484 : (((False ∧ ((((p2 ∧ ((True ∨ (False → (p4 → ((p4 ∨ False) ∨ (p2 → p3))))) ∧ False)) → (False ∨ p4)) ∧ p3) → p2)) ∧ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231488103908982416737200580595 : (((p3 → p3) ∨ True) → ((((p3 ∧ ((p5 ∨ (p4 ∧ p1)) ∧ True)) ∨ (p5 → ((p2 → (p5 ∧ p2)) → True))) ∨ (p3 ∨ p2)) ∨ (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165236142302684269772402580623 : (((True ∧ (((p5 ∨ p3) ∨ (((p5 ∨ p4) ∨ p4) ∧ p3)) ∨ (p5 ∨ p1))) ∨ (p2 → False)) ∨ ((False → ((p3 ∨ (p4 ∨ p4)) → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197831998387071887403565880444 : (((p4 ∧ (p1 ∨ p3)) ∨ ((p5 ∨ p3) ∧ p4)) ∨ (((p1 → (True ∨ ((True ∨ (p4 → ((p3 ∧ False) → p5))) ∨ False))) ∨ (p4 ∧ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256762305470413343406718354715 : ((p1 ∨ p2) → ((False ∧ ((((True ∧ p5) ∨ p2) → ((p3 → (False ∧ p3)) ∨ (p1 ∨ False))) ∨ (p4 ∨ (p4 → ((False ∨ p1) → p2))))) ∨ True)) := by
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
theorem thm_5_vars_200256211490102895978692508614 : (((p1 ∧ (p2 ∨ p2)) → ((p4 ∧ p2) ∧ p1)) → ((p1 → (((p5 ∧ (False ∨ p3)) ∧ (p2 ∧ False)) ∨ ((p5 ∧ p2) → (p4 ∨ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∧ (p2 ∨ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777070272643192535142874036046 : (((p1 ∨ ((p4 ∧ (p2 ∧ (((False ∨ p2) ∧ False) ∧ ((p2 → (p4 → (True ∧ (p1 ∨ ((True → p2) ∧ p4))))) ∧ p5)))) ∨ (False → p3))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695563404065601500975868964243 : (((((p5 → ((p3 ∨ p2) ∨ ((p2 → False) → p1))) ∨ (p5 → (True ∨ p5))) → ((((p3 ∧ True) ∧ (True ∧ p4)) ∧ p3) ∨ (p3 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586684373863048452053816928580 : (((((True ∧ ((True ∧ ((((p4 ∧ ((p1 ∧ p1) ∨ p3)) → (p3 ∧ p2)) ∧ p5) ∨ p5)) ∧ ((p3 ∨ p2) ∧ (p3 → p2)))) ∧ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343401631349462871419342261786 : (p2 → ((p3 ∧ p4) ∨ ((False ∨ (p4 ∨ (p1 ∨ ((p4 ∧ ((((p2 → False) ∧ (p4 → True)) ∨ True) ∨ (p3 ∨ p3))) ∨ (p4 ∧ p4))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54580073034148304780164091302 : (((p2 ∨ (((p2 ∧ p1) ∨ p4) ∨ (p1 ∧ True))) ∨ (False ∨ (((p5 ∧ True) → p4) ∧ ((((True → True) ∨ False) ∨ (p4 ∧ p1)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734792570579159690285904008331 : ((((p2 ∨ False) ∧ (False ∨ (p3 → ((p5 ∨ (p2 ∨ (((p2 ∨ (p5 ∨ p2)) → (True ∨ (p5 → p3))) ∨ (p4 ∧ (p4 ∨ True))))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341051460733522356694362336769 : (p2 → ((p1 ∨ (p1 → (((True ∧ (False → False)) ∧ p3) ∨ ((((False ∧ p5) ∨ p3) ∨ (p2 ∨ False)) ∨ (p4 → (p4 ∧ (p3 ∧ True))))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257702354973784326813142338417 : ((p3 ∨ p3) → ((p1 ∨ (p1 ∧ p4)) → ((p3 ∨ ((((((p1 ∨ True) ∧ p2) ∧ p2) ∨ (p4 ∨ p5)) → p5) ∧ (p3 ∨ False))) → (False ∨ True)))) := by
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
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48997942833865266385457757717 : ((((p4 ∨ ((((False ∧ ((False ∨ True) → ((p3 → p1) ∨ False))) ∨ False) ∨ (p2 → p4)) ∨ (False → False))) ∨ True) ∨ ((True ∧ p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304686939859358332977631716515 : (p1 ∨ ((((((((p2 → False) ∧ p4) → False) → (((p5 ∨ p3) ∧ (True ∨ (True ∧ p4))) ∧ True)) ∨ p1) ∨ (False → p5)) ∨ p3) ∨ (False ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186644713498887204572940063341 : (((p4 → ((False ∨ p1) → (p1 → (p3 ∨ p2)))) → (p1 ∨ p3)) → (p5 ∨ (((p4 → p1) ∨ (False → (False ∨ p4))) ∨ (p4 → (p3 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113801108929543082387577003153 : ((((p1 ∨ p1) → ((p3 → (p3 → ((True → (((((p2 → p1) → p5) ∧ False) → False) → False)) ∨ True))) ∨ p3)) → (p3 ∧ False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157205056289762014632661819817 : ((((p3 → ((False ∨ ((p3 ∧ (p3 ∧ p4)) ∨ p2)) ∧ (p2 ∨ (False → p5)))) ∨ (False → p2)) → p3) ∨ (True ∨ (p4 → ((p5 ∨ p1) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52577930965476470856345804372 : ((((((False ∧ p2) ∧ (False ∨ (True ∨ p1))) → (p1 ∨ True)) → (p2 ∧ True)) ∨ (True ∨ (p5 ∧ (True → (p5 ∨ (p1 ∨ (p5 → p2))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48608599354908088704116470691 : ((((p5 → ((p3 ∧ (((((p5 ∧ p3) ∧ p3) ∧ p4) ∧ (p4 ∨ p2)) ∨ p1)) ∧ (p5 ∧ False))) ∨ (p4 → p4)) ∧ ((p1 ∧ p5) → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324756097065756137462287129069 : (p5 ∨ ((False → (p3 ∨ True)) → (p1 ∨ (((((p3 → (p3 ∧ (True ∧ p3))) → (p4 ∧ False)) ∨ p4) ∨ (p3 → ((False ∧ p2) → p3))) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150184496782735159577639341087 : ((p1 → (p4 → ((((True ∨ p4) ∨ (((p3 ∧ ((p2 → True) → p3)) → p5) ∧ (p1 → p5))) → p3) ∨ p1))) ∨ (False ∧ (p1 ∨ (p1 ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150190493961305060485491301507 : ((p2 → (((False ∨ (((((p2 ∨ (p2 ∧ False)) ∨ p4) ∨ p1) ∧ False) ∧ (p5 ∧ (True ∨ False)))) ∧ p4) ∨ False)) ∨ (((True ∨ p1) ∧ p5) → p5)) := by
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
theorem thm_5_vars_118623548577093603814645703190 : ((p4 ∨ ((False → (((True ∧ p1) → p3) → (p3 ∨ False))) → ((((True → p1) ∨ p1) ∧ (((p2 → True) → p1) ∨ p1)) ∨ p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55241493011295302468638565572 : ((((p5 ∧ True) ∧ ((p2 ∧ p2) ∨ p4)) ∨ (((p3 ∨ (((p4 ∨ p2) ∧ (False ∨ ((p4 ∧ True) ∧ p1))) → False)) ∧ p4) → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166216623373277694827629614412 : ((p2 ∧ ((p2 ∧ (p3 → (p2 ∨ (((False → p5) ∧ (p5 ∨ (p5 → False))) → p3)))) ∨ p5)) ∨ (((p3 ∨ (p5 ∨ True)) → False) → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p5 ∨ True)) := by
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
theorem thm_5_vars_696310670426953145152190508879 : ((((p1 → (p4 ∧ ((p5 ∧ (False ∨ p1)) ∧ ((p5 ∨ (p1 → p3)) → p5)))) → ((p4 ∧ p1) ∨ (((p2 ∧ p4) ∨ p1) → (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257535242454077034908913477427 : ((p3 ∨ False) → (p4 ∨ (((p1 → (p4 ∨ False)) ∧ p4) ∨ ((p1 ∨ p5) → (((False ∨ (((False → p3) ∧ (False → p1)) ∧ p5)) ∨ p3) ∨ p2))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138212191426567111653320384097 : ((p2 → ((((False → (p4 → (p5 → p5))) ∧ ((p3 ∨ p4) ∨ (((p2 ∨ (p5 → p5)) → p4) ∧ True))) ∨ True) ∨ p4)) ∨ ((p5 ∧ p4) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890056673305085274317850480 : ((p2 → ((((False ∧ (False ∨ p5)) → ((p5 ∧ p5) ∧ p3)) ∧ ((((p4 → p2) ∨ True) → (p2 ∧ (p1 ∨ p5))) ∨ True)) ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338766169658211736560039786462 : (p1 → ((p1 ∧ p2) ∨ ((p3 → p4) → ((p5 ∧ ((p2 → (((p4 ∨ ((True ∨ (p2 ∧ p5)) → p4)) ∨ False) ∧ p3)) → False)) ∨ (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344478458610951260162146547197 : (p2 → (True → (((((False ∧ p1) ∧ ((p4 ∨ (p4 ∧ (p2 ∨ p1))) ∨ p3)) ∨ (p2 → (p2 ∨ (False → (p5 → p4))))) ∨ p4) ∧ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341045467777020210147807418030 : (p2 → ((False ∨ (p3 ∨ ((p1 → (p1 ∨ p1)) → (((p5 ∨ False) ∨ True) → ((((p5 ∨ p1) ∨ p5) ∨ (p5 ∨ p2)) → (p2 ∧ p5)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246184713118793856221341755361 : ((p4 ∧ p2) ∨ (p4 → (p2 → ((((((p4 ∨ p5) ∧ p5) ∧ ((p1 ∨ (p3 ∨ (((False ∧ p1) → False) ∧ p2))) ∨ True)) ∨ p4) ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55849541853623226249283611148 : (((p2 ∧ (True ∨ (True → p1))) ∧ (p3 → (False ∨ (p3 → ((False ∧ True) ∨ ((p5 ∧ ((p1 ∨ (p5 → p3)) → p3)) ∧ (p4 ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



