variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358071059998404452018236471588 : (p5 → (p1 ∨ (True ∧ (((p2 ∨ (True → (p2 ∧ ((p3 ∧ p1) ∧ (p5 ∧ ((False ∨ True) ∨ p3)))))) ∨ p5) ∨ (False ∧ ((p4 ∧ p3) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64536733328787479461968999639 : ((p1 ∨ ((True → ((p1 ∨ False) ∧ ((False ∨ False) ∧ True))) → (((p1 ∧ (False ∨ False)) ∨ ((p3 → p4) ∧ ((False ∨ p2) ∧ p1))) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154274373802660809227703554220 : ((((p5 ∨ p3) ∧ (((p5 → (p4 ∨ p4)) → p3) → ((p4 ∧ (True → p5)) ∧ (True ∨ True)))) ∨ True) ∧ (((p1 → (False → p4)) → p2) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901361245674716009928013372110 : ((((p5 → ((((True ∧ p1) → (p4 ∨ (p1 → p1))) ∧ (p3 ∨ p4)) ∨ (((p4 → p5) ∧ (p1 ∧ p2)) → p1))) → (p3 ∧ (p1 ∧ p5))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((((True ∧ p1) → (p4 ∨ (p1 → p1))) ∧ (p3 ∨ p4)) ∨ (((p4 → p5) ∧ (p1 ∧ p2)) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178602358093289640324667078710 : ((((p2 ∨ p5) → (False ∧ (p5 ∧ True))) ∨ ((False ∧ (p5 ∧ p2)) ∨ True)) ∨ (p5 → (p1 ∧ (((((p1 → True) ∧ True) → p2) ∧ True) → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309613213721134309740888709603 : (p2 ∨ ((((p2 ∨ (False → (((False → p1) → (p4 ∧ p1)) → p5))) ∨ (True ∨ ((False ∨ p3) ∨ (False ∨ p3)))) → False) ∨ (True ∧ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233735745246288973109270860137 : ((p3 ∨ (p3 ∧ p4)) → ((((((False → p5) → (p1 ∨ ((p5 ∨ (True → False)) → p1))) ∧ (p3 ∨ p5)) ∨ False) → (p3 → p4)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184586774703038233979674913832 : (((p2 ∨ ((((p3 ∨ p5) ∧ p4) ∨ False) ∧ p5)) → (True → p2)) ∨ ((((p3 → p4) → (False ∧ p3)) → (p1 → p4)) ∨ (True → (p5 → True)))) := by
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
theorem thm_5_vars_41595666789655123748259836750 : ((((((p3 ∨ ((True ∧ p1) → p4)) → p2) ∧ p3) ∨ ((False ∨ (((p3 ∧ False) → (p5 ∧ (p4 → p5))) → p1)) → (p3 ∧ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645386151557332859674855796641 : ((((p4 ∨ ((p4 ∧ ((True → False) ∧ (p5 → ((((False ∨ p1) ∧ False) ∧ ((True → p5) ∧ p2)) → (p4 ∨ p1))))) ∨ (p3 → p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218582242083814645481782921810 : (((p2 → p1) → (p2 ∨ p3)) → ((True ∧ (False ∧ (p2 ∧ p4))) ∨ ((p3 ∧ (((p2 ∨ p3) → False) ∨ False)) → (p3 ∧ ((True ∨ p5) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : (p2 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397800297306015988069068091212 : ((((p3 ∨ ((((False → p2) ∨ (((p1 → p1) ∧ p1) ∨ p2)) → False) → ((True ∨ ((p3 ∨ (p2 ∧ p5)) ∨ True)) → (p1 ∨ p2)))) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((False → p2) ∨ (((p1 → p1) ∧ p1) ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : ((False → p2) ∨ (((p1 → p1) ∧ p1) ∨ p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h10
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : ((False → p2) ∨ (((p1 → p1) ∧ p1) ∨ p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h17
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10452237714096859811496927323 : (((p1 → ((p2 ∨ ((((p2 ∨ (p5 ∨ True)) ∨ p5) ∨ (((p1 → (p4 ∧ p1)) ∨ p3) → p2)) ∧ (p3 ∧ p3))) ∨ (p5 → p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761813631262895702915399581977 : (((p3 ∧ (((((p2 → p1) → ((p5 → ((p2 ∧ p4) ∧ False)) ∨ ((p3 ∨ p2) ∧ (p4 ∧ p2)))) → (False ∧ (p4 ∧ True))) ∨ False) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119596693261434509522477495462 : ((p5 → (p3 ∧ ((((True ∨ (p2 ∧ ((((False → False) → p1) → p1) → p3))) → (p3 → (p1 ∧ p4))) → (p2 ∨ True)) → p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118384619057619093953742932537 : ((p2 ∨ ((((p5 ∧ ((p1 ∧ True) ∧ p5)) ∨ p1) ∧ p5) ∧ ((True ∨ (False ∧ (p5 → True))) ∨ (p4 ∧ (p1 ∧ (p2 ∨ False)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689487040059164586120543321233 : ((((((p1 ∧ ((False ∧ p3) ∧ p1)) ∨ (p2 ∨ (p4 → p1))) → ((p5 ∧ p4) → p3)) ∨ (((p2 → (False ∨ p4)) → p5) ∨ (p4 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165047647551336183320213882152 : ((((p2 → p4) ∨ (((((p5 → (p5 ∧ (p2 → p2))) → True) ∨ p5) ∧ p5) → p5)) → p5) ∨ ((p2 ∨ (p5 ∨ p3)) → ((False → p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117203364031089623684463029792 : ((True ∧ (((False ∨ p2) ∧ (p3 ∧ (p1 → (True ∨ (True ∨ p2))))) → ((((True → p2) ∧ p4) → (p1 → (p2 ∧ False))) → p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310662217133955529297098842394 : (p2 ∨ (((p1 → (p4 ∧ True)) ∨ p2) → (((p5 → ((False → True) → p5)) → (((False → p2) → p1) → p5)) → (p4 ∨ ((p2 ∧ p4) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345366574225149453540252185951 : (p3 → (((((p1 → (((p3 ∨ p3) ∧ p5) → p2)) ∧ (((p1 ∨ ((p1 ∨ True) → p5)) ∨ False) ∧ p2)) → ((p5 → True) ∧ False)) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737370402067779203655297415707 : ((((p4 → p3) ∧ ((p5 ∨ ((True ∨ p3) → (((True ∧ (p2 ∧ (((False ∨ p1) → p5) ∧ (p1 → p4)))) ∨ True) ∨ p1))) ∨ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45753282548583025920381446233 : (((False → ((False ∨ ((p3 ∨ ((p3 ∧ (p3 ∨ (p1 ∨ p4))) ∨ (p3 → (p5 → p2)))) ∨ p1)) ∧ ((False ∧ p4) → (p2 ∧ p1)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196957401029745817018508344353 : ((((False ∧ (False ∨ (p3 ∧ p5))) ∨ p2) ∨ True) ∨ ((p1 ∧ (((p2 → p1) ∧ p3) → p3)) → (p1 ∧ ((p3 ∧ (p3 ∨ (p2 → p4))) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647992871100196357371750456601 : (((((((p3 → ((p3 ∧ (True ∨ (p2 → p4))) ∨ p1)) → (p2 ∨ ((False ∧ p1) ∨ p3))) → (p1 ∨ (p5 → p1))) ∧ True) ∧ (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221136080303651949253798160442 : (((True ∨ p3) ∨ True) ∧ ((p4 ∨ ((p2 → ((False → p2) ∨ (p3 ∧ False))) ∨ (p4 → p4))) → ((((True ∨ True) ∨ False) → (False ∧ p3)) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((True ∨ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : ((True ∨ True) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : ((True ∨ True) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962372456728732501832662877994 : ((((True → True) ∧ (((True → (p3 → (p2 → (p3 → True)))) ∨ p2) → ((((p2 ∧ (p3 ∨ ((False → p4) ∨ p3))) ∧ True) ∧ False) ∧ True))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (p3 → (p2 → (p3 → True)))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382986172398774832536351299380 : (((((p2 ∧ ((((p2 ∨ ((p2 ∧ False) → (False ∨ False))) → (((p2 ∨ (p3 → p5)) → p3) ∨ p5)) → (False ∧ p3)) → p3)) ∨ True) ∨ p2) ∧ True) ∧ True) := by
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
theorem thm_5_vars_336228800717638331542517361635 : (p1 → (((p2 → ((p1 ∧ (False ∨ (p3 ∨ (p4 ∨ (p5 → (p1 ∧ p3)))))) → ((True ∨ p5) ∧ (p4 ∧ p5)))) ∨ ((p5 → p1) ∨ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245619605207433543054263453629 : ((p3 ∧ False) ∨ ((False ∨ p1) ∨ (p3 → ((((p3 ∧ False) ∨ (((False ∨ (False ∨ (p4 → True))) ∧ True) ∧ p5)) ∨ ((p1 → p5) ∨ True)) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118165538432778733146153569122 : ((False ∨ ((p4 ∨ p2) ∧ (p4 ∨ ((p4 ∨ (False ∧ (p2 ∧ p4))) ∨ ((p4 ∧ (p2 ∧ True)) ∧ ((True → (True ∧ p2)) ∨ False)))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349082521215068270441393939042 : (p3 → (p5 ∨ (p3 → ((p5 ∨ (p4 ∨ p1)) → ((((p2 ∨ (p3 ∧ (p4 ∧ True))) ∧ p4) ∧ p1) → (False ∨ (p3 ∨ (p1 ∧ (p3 ∧ True))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256520121077216498109010179987 : ((False ∨ p5) → ((p3 ∨ (((False ∨ p4) → (p4 ∨ (p5 ∨ (((p4 ∨ ((((p2 ∧ p5) → p1) ∨ False) → p3)) → p3) ∧ p4)))) → p3)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132925433999395429851625521074 : ((p4 ∨ (((p5 ∨ p4) → ((p5 ∨ (p4 ∨ ((p2 → p2) → p1))) ∧ (p4 ∨ ((p3 ∨ (False ∧ True)) ∧ p3)))) ∨ True)) ∧ (p4 ∨ (True ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354675300863000626779913976102 : (p5 → (((p5 → (((((((p3 → ((False ∧ p5) ∧ (True ∧ True))) ∨ p3) ∨ (p2 ∨ (False ∨ p4))) ∨ p1) ∧ p4) → p5) ∨ p2)) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61802206272157911652913875488 : ((p2 ∧ (((((False ∨ (p1 → (p5 → (p1 ∨ p4)))) ∨ ((p5 → p5) → ((p3 → p5) ∧ ((p4 ∨ p2) ∧ p3)))) ∧ p4) → p5) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37088404562587508015783068346 : ((((((p3 ∨ p5) ∧ (True ∧ ((p1 ∧ (True ∧ ((((p2 → p3) ∧ p5) ∧ (p4 ∧ False)) ∧ p1))) ∧ (p2 ∧ p2)))) ∨ p5) ∧ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181363535343667470729750579268 : ((False ∨ (False ∨ ((((p4 ∨ (p5 ∨ (p5 ∧ p4))) ∧ p3) ∧ True) ∨ True))) → (((p5 ∨ (True ∧ p4)) ∧ False) ∨ (p2 ∨ ((True ∧ p2) ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147624515635297742783728526048 : ((((((((p2 ∨ (((p5 → p1) ∧ True) ∨ p5)) ∨ p2) ∧ p4) → ((p2 → p3) ∨ p2)) → p2) → p5) → p4) ∨ (True ∨ (p1 ∧ (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329200551295408011918515747227 : (True → (((True ∧ p1) ∨ True) ∧ (((True → False) ∧ (True ∨ p1)) → (((False ∨ p4) ∧ True) ∧ ((p2 → p1) ∧ (p5 → ((False ∨ False) ∧ p2))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h23 := h19 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h26 := h19 h25
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h2.left
  let h28 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h29 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h31 := h27 h30
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h34 := h27 h33
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171582606751040574073230969303 : (((((p1 → p4) → ((False → (p5 ∨ False)) ∨ (False → p5))) → (p4 → p5)) ∨ p4) ∨ ((p4 ∨ p5) → (p1 → (((p1 ∧ p2) → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_346298959760249836717822046978 : (p3 → (((True ∧ (p3 → (p1 ∨ (p4 → ((p4 ∨ p4) → ((p5 ∨ (((p4 → False) ∨ p1) ∨ (False → p3))) ∨ p3)))))) ∨ p2) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115051626916372134773592452806 : ((((False ∨ ((p1 → (False ∧ p2)) ∨ ((p4 ∨ True) ∧ False))) → p1) ∨ (((True ∧ (p2 ∨ False)) ∧ p3) ∨ (p3 → (p4 ∨ False)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262441078045877181429722307690 : (True ∧ ((p5 ∧ ((p1 ∨ (p2 ∨ p5)) → (p3 → ((p5 ∨ p3) → (p1 → (((False ∨ p4) ∧ ((False ∧ (p1 → p2)) → p5)) ∨ p3)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300895264912999821823606154738 : (False ∨ (((((p3 → p3) → False) ∧ (p4 → (False → (True ∨ (p4 ∧ p4))))) ∧ p1) → (p2 ∧ ((False ∧ p2) ∧ (p2 ∧ (False ∨ (p2 ∧ p3))))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h20 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h22 := h18 h20
  -- False on the left can always be used.
  apply False.elim h22
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
  have h27 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h28
    -- One of the premise coincides with the conclusion.
    exact h28
  -- We have shown the premise of h25, we can now drive its conclusion.
  let h29 := h25 h27
  -- False on the left can always be used.
  apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
  have h34 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h35
    -- One of the premise coincides with the conclusion.
    exact h35
  -- We have shown the premise of h32, we can now drive its conclusion.
  let h36 := h32 h34
  -- False on the left can always be used.
  apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626504089743293367238414823643 : ((((p4 → ((((p1 ∧ p2) ∨ p4) ∧ (((p1 ∨ (True ∧ p4)) → (True → p2)) ∨ ((p2 ∧ p5) ∧ False))) → (p2 ∧ (p3 ∨ p2)))) ∨ p3) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (True ∧ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- False on the left can always be used.
      apply False.elim h33
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h37 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : (p1 ∨ (True ∧ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h40 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h41 := h39 h40
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- Conjunctions on the left can always be decomposed.
      let h45 := h43.left
      let h46 := h43.right
      -- False on the left can always be used.
      apply False.elim h44
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157044350337014334135898990143 : (((False ∧ (((((p3 ∨ p3) → p2) → True) ∨ False) ∧ (p1 → (((p4 → p3) ∨ p3) → p4)))) ∨ p2) ∨ (True → ((p5 ∧ (False ∧ p4)) → p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158568677376577626736793534417 : ((True ∧ (((True ∨ (p4 ∧ (p2 ∧ (p1 → p3)))) → ((p2 ∧ False) ∨ p4)) ∨ (p5 ∧ (False → p1)))) ∨ (((p3 ∨ (p5 → True)) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607551416256526197091368318635 : (((((False ∧ (p1 ∨ ((p4 ∨ p2) ∨ (((((p5 ∧ ((p5 ∧ (p4 → p4)) → True)) → p1) ∧ True) ∨ False) ∨ (False ∨ p1))))) ∧ True) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41515033143484164968510442078 : (((((((False ∨ p5) ∨ True) ∧ (p4 → (p5 → True))) → p5) ∧ (((p1 ∨ p1) → True) ∧ (((True → p3) → p5) → (p2 ∧ p5)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217135495570368273634823114393 : ((((False → False) ∨ p5) ∨ False) → (True ∧ (p2 ∨ ((False ∨ p2) ∨ (p4 → (((p3 → p4) ∨ p2) ∨ ((p4 ∨ (p4 → p4)) ∧ (p5 → p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111072861824009722732078280992 : ((((((p2 ∨ ((((p4 ∨ p4) → p2) ∨ p3) ∨ (p2 ∨ p2))) ∨ p1) ∨ p2) → (((False ∨ (True ∧ p3)) ∨ p1) → False)) ∧ p5) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595095535626734191446898004294 : (((((p2 → ((False ∨ p3) ∧ (p1 ∨ ((p4 → p2) → ((p3 → p5) → False))))) ∨ ((p2 ∧ p4) ∧ (True ∧ ((p5 ∧ p4) → p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186403864039351306179269816190 : (((True ∨ (p3 ∨ (p1 ∧ ((p4 ∨ p4) ∧ (False ∧ p1))))) → p5) → (((p4 → (p1 ∧ True)) ∨ (True ∨ (p3 → (False → True)))) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64318336183410458629614678131 : ((p1 ∨ ((((p1 ∧ ((p4 ∨ (p3 → ((p2 ∨ (p5 ∨ p1)) ∨ (p5 ∨ (p3 → p5))))) ∨ p5)) ∧ (p5 ∨ p1)) ∨ (True ∧ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808407696973067366613586991073 : (((p4 → (p2 ∨ ((((p2 ∨ p5) ∨ False) ∧ (False → (p2 → (p5 ∧ (((True ∧ (False ∨ True)) → ((False ∧ p3) ∨ p1)) ∧ p1))))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741429740198363211240696563749 : ((((p5 ∨ p1) ∨ (((((p3 → (False ∨ p5)) ∧ (p5 ∧ p2)) ∧ p3) → ((p4 ∨ p4) → p1)) → ((True ∨ p4) ∧ (False ∨ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213639636820920459237399442877 : ((((False ∨ p3) ∨ p5) ∨ False) ∨ ((False ∨ (p2 → ((p5 → (p5 ∧ ((p4 ∧ False) ∨ p1))) → (p5 ∨ p2)))) ∨ (p3 ∧ (p5 → (p5 ∧ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50311751572780115035300625860 : (((((p4 ∧ p5) → ((((p2 → False) → p1) ∨ (True ∧ p1)) → p3)) ∨ (True ∧ (p5 ∨ (p4 ∨ True)))) ∨ ((True ∧ True) ∧ (p3 ∨ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41340272229270691787182260979 : (((((((False ∨ p1) ∧ (p5 ∧ (p3 ∧ p4))) ∧ True) ∧ ((p4 → p3) ∨ (p1 ∨ p2))) ∨ (p1 → (((p4 ∧ p2) → p3) ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356430824879772916216852309001 : (p5 → (((((p2 ∧ (p2 → p5)) ∧ False) ∨ ((p2 → p5) ∧ p2)) ∧ False) ∨ (((p4 ∨ p2) → (False ∨ (p4 ∧ False))) ∨ ((p2 ∨ p2) → p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669836165480830877860691726688 : ((((((False → p4) → ((p1 ∧ ((p4 ∧ False) ∨ (p3 ∧ False))) ∨ False)) ∧ (((p4 ∧ (p5 → p4)) ∧ p1) ∧ True)) ∨ (p2 ∨ (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207740626057246355968874780346 : (((p5 ∧ (True ∨ (p4 ∧ True))) → p4) → (((p3 ∨ p4) ∧ (p4 → (((True → False) ∧ (p5 → p1)) ∧ False))) ∨ (p3 ∨ ((p5 ∨ p3) → True)))) := by
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
theorem thm_5_vars_314602008035619730534221662229 : (p3 ∨ ((True → (((p5 ∨ ((p2 ∨ p3) → p4)) ∧ ((True → p1) ∨ p4)) ∨ (p4 ∧ (p2 → False)))) → (((p1 ∨ True) → (False ∧ p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173686517721893791594605135421 : ((((p5 → (p4 ∧ (((False ∨ p2) ∧ p3) ∨ (p5 → (p4 ∧ True))))) ∨ True) ∨ p3) → ((p4 ∧ ((p3 → p2) ∨ (p3 → False))) ∨ (p1 → p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225984301062899021622773125920 : (((p3 ∧ p4) ∨ False) ∨ (p1 ∨ (((p1 → ((p1 ∧ (p5 ∧ p3)) ∨ False)) ∨ p3) → ((((True → True) → False) ∨ (p1 ∨ True)) ∨ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305889912216939984148455397503 : (p1 ∨ ((p2 ∨ ((p3 ∧ p2) ∨ (p3 → p1))) ∨ (True ∨ (p4 ∨ ((((True ∧ ((p3 ∧ p4) ∨ (p3 ∨ p2))) ∧ p3) ∨ (True ∨ p3)) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137638339271313673390086298604 : ((False ∨ ((p2 ∧ (((p5 ∨ p4) ∨ True) → (((p4 → p2) ∧ (p5 ∧ p2)) ∨ p1))) ∨ (((True ∧ True) ∨ p5) ∧ False))) ∨ ((True → p3) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43002327746916041839676666738 : ((((((((((p4 → (True ∧ (((False ∧ True) → (p1 ∨ p3)) ∧ True))) ∧ p3) ∨ (p2 ∨ p3)) → p3) ∧ p4) → p4) ∧ p2) ∧ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181050777290971919387803693385 : (((p1 ∧ p3) → ((p5 → p1) → ((p2 → (p4 ∧ p3)) → (p5 → p5)))) → (p4 → ((p4 ∨ ((p4 → (p3 ∧ False)) ∨ p3)) → (p5 → p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62016236349871406245430900063 : ((p2 ∧ ((p2 → (p1 ∧ p2)) ∧ (False ∨ (p2 ∧ ((p2 → (((False → (((False ∧ p1) → p4) ∧ p4)) ∨ p2) ∧ (p4 → p2))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650245911268661919132010790645 : (((((((True → False) → ((p2 ∧ (p4 → ((p1 → True) ∨ (False → p2)))) ∧ p3)) ∧ p4) → ((p2 → p2) ∧ (p1 ∨ p2))) ∧ (False → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38766990014296803166470394027 : ((((False → ((p5 ∧ p4) ∧ p3)) ∧ (((p5 → (((p5 → ((p5 → p1) → p1)) → False) ∨ True)) ∧ p2) ∧ (False → (p4 → p5)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460048851922338558779955891822 : (((((p3 → p5) ∧ ((p3 ∧ ((p4 ∧ ((p4 → (p1 → p1)) ∨ False)) → False)) ∧ (True ∨ True))) → ((p1 ∨ (p4 → (p4 → False))) → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h23 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h24 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h25 := h17 h24
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h27 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h28 := h17 h27
      -- One of the premise coincides with the conclusion.
      exact h28
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326921972952835000719915620285 : (True → ((((True ∨ (True → p4)) ∧ ((p3 ∨ p3) → (p5 ∨ (p3 → (((p3 → True) ∨ ((p5 ∨ p4) → p5)) ∨ (p4 → p1)))))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328137295333063156891076117390 : (True → (((p4 → p1) → ((p5 ∧ (((p4 ∨ (p1 ∧ (True → ((True ∨ p5) → (p4 → p2))))) ∧ p3) → p2)) → p1)) ∨ (p2 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_692910711645938247192079615938 : (((((p5 ∨ False) ∧ ((False ∨ (p3 ∨ ((p5 ∧ (p5 → p4)) ∧ True))) → p1)) ∧ (((p1 → p4) ∧ (False → ((False ∨ True) ∧ p4))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950607312405404250513277499719 : ((((p1 ∧ (p1 → False)) ∧ (((p4 ∧ (p1 ∨ (((p4 → False) ∨ p5) ∧ ((True ∧ p2) ∨ p2)))) → p2) ∨ (p5 ∧ (p1 ∨ (p1 ∧ p2))))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681024498538405455733101306882 : (((((p5 ∧ False) → ((((((p4 ∧ False) ∨ p4) ∧ (False → (p2 ∨ p5))) → True) ∧ p2) ∨ (False → True))) → ((p3 → (True ∨ p3)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40036326170494048483595914647 : (((((((p2 ∨ (p3 → p2)) ∨ p5) ∨ ((True → False) → ((p3 → p3) ∨ ((True ∨ p2) ∧ (p3 → (True → False)))))) ∧ p3) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339046521792930492240606433048 : (p1 → (True ∧ (p3 → ((((True ∨ False) ∧ (p2 ∨ ((((False → p4) ∨ (p2 → False)) ∨ p1) → ((p1 → (p4 ∨ p5)) ∧ p1)))) → p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348806274130991886786148560770 : (p3 → (p1 ∨ ((p2 → (((p5 → p1) ∨ p1) → ((p1 → ((False ∧ p4) → (p3 ∨ p1))) → (p5 ∧ p5)))) ∨ (p1 → ((False → p1) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41482764118162785310274114667 : ((((p1 ∧ ((p3 ∨ (((p5 → (p3 ∨ p1)) ∧ True) ∧ p4)) ∨ False)) ∨ (False ∧ (((p1 → (False ∧ p4)) → (p5 ∨ p3)) ∧ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324005376561667450490293092935 : (p5 ∨ ((p4 ∨ (False ∨ (False ∨ (p1 ∨ (p5 ∧ ((True ∧ p2) ∧ (False → p1))))))) ∨ (((True → False) → (p2 ∧ p2)) → ((p4 ∨ True) ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217103134240034509711603938572 : ((((p5 ∧ p2) ∨ False) ∨ p3) → (((p1 → p5) ∨ (p2 ∨ (((p3 ∧ False) ∨ p4) ∨ (p5 ∨ (p4 → ((p3 → p5) ∨ p4)))))) ∨ (True ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113563904488582950604457990892 : ((((p2 ∨ p5) ∨ ((p2 ∨ ((((((p1 ∨ False) ∧ (True ∧ p1)) ∧ p5) ∧ p5) ∨ p4) ∨ p5)) ∨ (p4 → True))) ∨ (False ∧ True)) ∨ (p2 → p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192134702096469969180638015076 : ((p5 → ((p1 ∧ p4) ∨ (False ∨ (p2 → (p4 ∨ p4))))) ∨ ((((p5 → p5) ∧ True) ∨ (p5 ∧ True)) ∨ (((p5 → p2) ∧ p4) → (False → p4)))) := by
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
theorem thm_5_vars_699693565026422487666156674880 : (((((True → (False ∨ (p4 ∧ (((p2 ∨ p2) ∧ p4) → p2)))) → p3) → ((((((p1 → True) ∧ p3) ∨ (False ∨ p2)) → p1) ∨ False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807847389815158500998666954065 : (((p4 → ((p3 → False) ∧ (((p4 → ((p1 ∨ p2) ∨ True)) ∨ p4) → (((True ∨ p1) → p5) → ((False ∧ (True ∨ p1)) ∧ (p2 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42592303058036107651721725030 : (((p2 ∨ ((p3 ∨ True) → (p4 ∨ ((p4 ∧ p3) ∨ (p4 → (False → (False ∧ ((p4 → p3) ∧ (False ∧ (False ∨ (p5 → p1))))))))))) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49942729190626498541546306096 : ((((p1 ∨ (p2 → (p1 ∧ (p5 ∨ ((p5 ∧ True) ∨ ((p2 ∨ p5) → (False ∨ False))))))) ∧ (p4 ∨ p4)) ∧ (((p2 → True) → p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336078126099450720633543311640 : (p1 → ((((((p2 ∧ p5) → (False → True)) ∧ (p3 ∧ (p5 ∨ ((p5 ∧ (p2 ∧ (p4 → p1))) ∨ (p3 ∨ True))))) ∨ (p4 → p5)) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1561632398984311835765913658 : ((p5 ∨ (p1 ∧ (p2 ∨ ((((((False → p2) ∨ (((p4 ∧ True) ∧ (p1 ∨ p2)) → p5)) → p4) → p3) → p1) → p5)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56183070606206600794727505064 : (((p3 ∧ (p1 ∨ (False ∨ p1))) ∨ ((((p1 ∧ p4) ∨ (False → p5)) → p4) → ((p1 → (p2 → p4)) ∨ ((True ∨ p1) ∨ (p2 ∨ p1))))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337374700619359224717208829558 : (p1 → ((((False ∧ p2) ∨ (False → p2)) → ((True ∧ (p5 ∨ p2)) ∨ ((False ∨ ((p5 ∧ (False → p1)) ∧ p4)) ∨ p1))) ∨ (p2 → (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83365452254442180238310765315 : ((((False ∨ True) → (((p5 ∧ (False ∨ (False ∧ p1))) ∧ (True ∧ (False → p1))) ∧ (p2 ∧ p1))) ∧ ((p3 → ((True → p5) ∧ p4)) ∨ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259313741792290873867418064515 : ((False → p2) → ((p3 ∨ (p5 → (((((p3 → (((p5 → False) ∨ p3) ∨ p3)) ∨ ((p2 → p1) → p4)) → p1) ∧ False) ∨ (True ∧ p5)))) ∨ p3)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803360924985609641865652180085 : (((p3 → ((True ∧ ((((p4 ∨ p5) ∨ (((p4 ∧ False) ∧ (p4 ∧ ((True ∧ (p4 ∧ p2)) → (p5 ∨ p3)))) ∨ p4)) ∧ True) ∧ False)) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317721252477570438692495514291 : (p4 ∨ ((((True → p5) → (((p1 ∧ p5) ∨ False) ∧ ((((True ∧ (p3 → p5)) → ((p5 ∧ p2) ∧ p3)) ∨ False) ∧ p3))) → (p1 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129207196674602790893758102347 : ((((p4 ∧ (((True ∧ (((p1 ∨ (p4 → p2)) ∧ p2) → p5)) → p1) ∧ p4)) ∧ ((True ∧ p2) ∨ (p3 ∨ p4))) ∨ True) ∧ (p2 ∨ (p5 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



