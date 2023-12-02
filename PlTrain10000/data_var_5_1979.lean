variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59366463953608861617062211493 : (((p5 ∨ p3) ∨ (p4 → ((((True ∨ True) ∧ (((True ∨ (True → ((True ∨ p4) ∧ p5))) → True) → p3)) ∧ ((p3 ∧ p1) → p3)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693808764870687000680605808544 : ((((((((p3 → False) ∧ ((False ∨ p1) ∧ p3)) ∨ p5) → (True → False)) → p3) ∨ ((((p1 ∨ ((p2 → True) → True)) ∨ p4) ∨ p2) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810875693675023090896957735980 : (((p5 → ((p3 ∨ p2) ∨ ((p1 ∨ p1) ∨ ((p4 ∨ (p5 ∨ p5)) ∨ (p2 ∧ (((False → (p2 ∨ p3)) ∧ ((True ∨ False) ∧ p5)) ∧ p5)))))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258805591026987085585359798384 : ((True → False) → (p5 ∧ ((((p5 ∨ p5) → (p4 → (False ∨ False))) → (p4 ∧ ((p4 ∧ (p4 → (p3 → p4))) ∨ p1))) ∨ ((p5 ∨ True) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668937310157391205664221000401 : (((((p1 ∨ (((p2 ∨ (False → (True ∧ p5))) ∧ (p1 → p4)) → (p1 ∧ (False ∧ (p5 → (p5 ∧ p2)))))) ∨ True) ∨ ((False ∨ p3) ∧ False)) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750341647753683553694388763347 : (((True ∧ ((((p3 → ((p5 ∧ (False ∧ p2)) → (p4 ∧ False))) ∨ p2) ∨ (True ∧ ((((p4 → True) ∨ p4) → True) ∧ p4))) → (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117142501751359423281893945478 : (((p5 → p5) → ((((p1 ∧ ((p3 ∧ p2) → p4)) ∨ (p1 → p2)) ∨ p4) ∨ ((True → ((False ∧ p4) ∧ (p5 ∨ p2))) ∧ False))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115350084478933775826941667710 : (((((p1 ∨ (p4 → (False ∨ p1))) ∨ p5) ∧ p3) ∧ (p1 → ((((((False ∨ p2) → (p5 ∨ p4)) ∨ p1) ∧ False) ∧ p2) ∧ True))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758925038275394654059697184184 : (((p2 ∧ (((((p3 → p5) ∧ (True → (((p4 → (p2 ∧ p2)) ∧ False) ∧ p2))) ∨ p1) ∨ (p3 ∧ (p5 ∧ ((False → p2) → p4)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58430649347831488235809383250 : (((p2 ∨ p5) ∧ ((p1 ∧ ((p4 → p2) ∧ (False ∧ p2))) ∨ ((p5 → p1) → (((p3 ∧ p3) → True) ∧ (False → (p2 ∨ (p1 ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52821923173411217501931246348 : ((((((p5 ∨ p4) → p1) ∨ p5) → (False ∨ ((p2 → (p3 ∨ p3)) → p4))) → (p2 → (p4 → (p5 ∨ (((p4 ∧ False) ∧ True) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200682845728150436048730558726 : ((p2 ∧ ((((p4 ∨ p4) ∧ p5) → p5) ∧ p5)) → ((((p4 ∨ (p3 → p3)) → p5) ∧ (((True ∧ True) → (True ∧ (p5 → False))) ∧ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1997135075249390411375398704 : ((((p1 ∧ False) ∨ (((p1 ∨ (p5 ∨ (p4 → (True ∧ (False ∧ True))))) ∨ False) → p3)) ∧ (p2 ∧ p4)) → ((p2 ∨ p4) → (p3 ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h14.left
      let h20 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228084564000738899500224885931 : ((p4 ∧ (True ∨ p4)) ∨ ((((p4 → ((p4 ∨ False) ∨ p2)) → p5) ∧ (p2 ∨ (((False ∧ p2) ∨ p2) ∨ (p4 ∨ p3)))) ∨ ((p1 ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136314646764889691362231882649 : ((((p3 ∨ (p1 ∨ False)) ∨ p2) ∧ ((True ∨ (((False ∨ p3) → (False → p4)) ∨ p4)) → (((True ∨ True) → p5) ∧ p4))) ∨ (p4 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165099600943165584929013480055 : (((p5 ∨ (True → (((((p1 → (False ∨ p2)) → p5) ∨ p1) ∨ (p1 → True)) ∧ p4))) → p2) ∨ (p5 → ((((p5 → p3) → p1) ∨ False) → p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116215794619702548006069575567 : ((((p5 ∧ p1) ∨ p5) ∨ ((((False ∧ (((True → p5) ∨ p5) ∨ ((p3 ∧ (p1 ∨ p2)) ∧ p4))) ∧ p4) ∧ (p1 ∧ False)) ∨ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807971941019204508298428641440 : (((p4 → ((p2 ∨ True) → (p3 ∨ ((p1 → (((p4 ∨ (((True → ((p2 → p5) ∧ p2)) → p4) ∨ p5)) ∧ p3) ∨ (False ∧ p4))) ∨ p4)))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623983196207778783413005242932 : ((((p2 ∨ (((False ∧ p4) ∨ (p4 → (True ∨ ((((True → (p2 ∨ p1)) ∨ (((p3 ∨ True) ∧ p5) ∧ p4)) ∧ False) → True)))) → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135305391118619630212668146998 : ((((p4 → ((p4 ∧ p1) ∧ (((p5 → (p3 ∧ False)) ∧ (p5 ∧ (p2 → p2))) → False))) ∨ True) ∧ ((p4 ∧ p1) → p4)) ∨ ((p2 ∧ False) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311822030112147728898268734289 : (p2 ∨ (p1 ∨ ((((False → p1) → ((False → ((True → ((True → p3) ∨ False)) → (p3 → p4))) ∧ p3)) ∨ p2) → (p4 ∨ ((p2 ∨ p3) ∨ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136462880279231954339361433176 : (((p4 → (p3 ∨ (True ∧ True))) → (((p5 ∧ (p4 ∨ (p1 ∧ p1))) ∨ (False ∨ (p5 ∨ False))) ∨ (p2 → (p4 → p2)))) ∨ ((p1 ∧ p5) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684131002155130316385183860625 : (((((p5 ∨ ((p1 → ((True ∨ p2) ∧ (p5 ∧ (p4 ∨ p2)))) ∧ (p3 → p3))) ∧ (p3 ∨ False)) ∨ ((p5 ∧ p5) → (p4 → (p5 ∨ p1)))) ∨ p4) ∧ True) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147853866614243817147500883172 : (((True → ((p2 → p5) ∨ (p1 ∧ ((p4 ∧ p1) → ((p2 ∧ (p4 ∧ ((p4 ∨ True) → p4))) → p1))))) → p2) ∨ (((False → False) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256474670796912272396828818712 : ((False ∨ p4) → (((((p3 ∨ ((True ∧ True) → (True → (p4 ∨ p4)))) ∨ p1) ∨ p3) → (p1 ∧ (p5 → p5))) → (p1 ∧ (p3 ∨ (p5 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p3 ∨ ((True ∧ True) → (True → (p4 ∨ p4)))) ∨ p1) ∨ p3) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h5
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (((p3 ∨ ((True ∧ True) → (True → (p4 ∨ p4)))) ∨ p1) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h15
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110189944169947191079657757530 : ((p1 → ((p2 → p3) → ((((p4 → p5) ∨ p1) → False) ∨ (p1 ∨ ((p5 → p1) ∧ (p5 ∧ (p5 → ((False ∧ True) → False)))))))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118277325923060331911096405449 : ((p1 ∨ ((True ∧ (p5 ∧ p4)) ∧ ((True → True) → ((p4 ∧ ((((p1 ∧ (p1 ∧ p1)) → p3) → p2) ∧ p4)) ∨ (p5 → p4))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44668972962094413265408673304 : ((((((p5 ∨ (p5 → False)) ∧ p3) ∨ p4) → ((p4 ∨ (((True → p4) ∧ p4) ∧ (False ∨ True))) → (((p3 ∨ p3) ∧ False) ∧ p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721305297333417432855564856833 : (((((p2 → p4) → (p2 → p2)) → (((True → p2) → False) ∨ ((p3 ∧ p4) ∨ (False → ((((p4 → False) ∧ p1) ∨ (p3 ∨ True)) → p3))))) ∨ p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170668159641578733846097828155 : ((True ∧ ((p4 → (p5 ∨ (p2 ∨ ((False ∧ ((False → p3) → p3)) ∨ p1)))) ∨ True)) ∧ (((p4 → p3) ∨ (False → (p4 ∧ p3))) ∨ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181397219905581943778029412905 : ((p1 ∨ (p3 → ((p2 ∨ (False → (p1 ∧ True))) ∧ ((True ∧ p4) ∧ p3)))) → (((p2 → p3) → p1) ∨ (True ∧ (False ∨ (p1 ∨ (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244856570756613204695962509364 : ((p1 ∧ p2) ∨ (((p1 ∧ ((p4 ∨ (((p2 ∧ ((p1 ∨ (p2 ∧ p5)) → (p5 → p1))) → p4) ∧ ((p4 ∨ p4) ∨ p3))) ∨ p4)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725572730787282823783128870030 : (((((p2 ∧ p2) ∧ True) ∨ (((p2 ∧ p3) ∨ ((False ∧ (p4 ∧ p4)) ∨ (p1 ∨ True))) ∨ ((p2 ∨ (True ∧ ((True → p3) ∧ p3))) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_231653797624242281318734036963 : (((False ∧ p4) → p2) → ((False ∧ ((p2 ∨ p3) ∧ p1)) ∨ (p3 ∨ ((((p1 ∨ ((p2 → p4) → p4)) → (p1 → True)) ∧ (p5 ∨ p4)) ∨ True)))) := by
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
theorem thm_5_vars_57078328083924662983498042586 : ((((False ∧ True) ∧ p2) ∨ ((((False ∨ (False ∨ False)) ∨ p5) → (((((p4 ∧ False) ∨ p3) → False) ∨ p1) ∧ (p1 → p2))) → (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349914284793156738943691308519 : (p4 → ((p2 → ((((p2 → p1) → ((p5 → (p3 ∨ True)) ∨ (p2 → p1))) → (p3 → ((p2 ∨ p5) → False))) ∨ ((p1 ∨ p1) → p1))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105142820310196747375427873747 : (((((p2 ∨ (p5 ∧ False)) ∧ (p3 → p1)) ∨ (((p3 ∧ False) → (True → ((False ∨ p3) → p4))) ∧ False)) ∨ (p2 ∨ (True ∨ p2))) ∧ (p3 → p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54237839969662901207604351718 : ((((p1 → (p4 → (p3 ∨ (p3 ∧ False)))) → p1) ∧ (False ∧ ((((False ∧ (p5 → p4)) → True) → (False ∨ (p2 ∨ p3))) ∨ (p3 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139353459387478836315477468919 : (((True → ((p5 ∨ (((p2 → True) ∨ p4) → (p3 → (p2 → ((False → ((p2 → True) ∧ p5)) → p5))))) → True)) ∨ p2) → ((p2 → False) ∨ True)) := by
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
theorem thm_5_vars_184956884263475341313084309559 : ((((p3 ∧ p1) → True) → (p5 ∧ ((p2 ∨ p5) ∨ (False ∨ p4)))) ∨ (True ∧ (False → (((p3 ∨ (True ∧ ((False ∨ p5) ∨ p2))) ∨ p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188841351874193299102806573089 : (((((p2 ∨ p2) ∧ p4) → False) ∨ (p5 ∨ (True ∨ p1))) ∧ (((p4 → (((True ∧ p5) ∧ True) ∨ p5)) ∨ p4) → (p5 → (p1 ∨ (p3 → p3))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248854138814135235992879935627 : ((p3 ∨ p4) ∨ (p1 → ((p4 → (p1 ∧ p1)) ∧ ((p3 ∧ p2) ∨ ((p2 ∧ (p2 → (True → (p3 → p3)))) ∨ (False ∨ ((p1 → True) ∨ p1))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755205792612367818933670675769 : (((False ∧ (p4 → (((False ∧ (p2 ∨ True)) ∨ (((p1 ∧ True) ∧ (p1 ∨ p1)) → ((False → p1) → (p3 → ((p4 ∨ p2) → p4))))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118495651848483240747208592228 : ((p3 ∨ (((p1 ∨ True) → ((p2 ∧ p3) ∨ (((p5 ∧ p1) → False) → (True ∨ p3)))) ∨ (p4 ∨ ((False ∧ p1) ∧ (True ∧ p5))))) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114890192558988321554494896387 : (((p5 ∧ (False → (p5 → ((True → ((p1 ∨ p2) ∨ (p4 ∨ p1))) ∨ p4)))) ∨ (((p2 ∨ (False → (p2 ∨ p2))) ∨ p3) → p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160253404299127166897112689446 : (((True ∧ ((True ∧ p1) ∧ ((p2 → p2) ∨ ((p3 ∧ False) ∨ (p5 ∨ (p4 ∧ p4)))))) ∨ (p3 → p3)) → (p4 ∨ ((False ∨ (False → p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- False on the left can always be used.
          apply False.elim h17
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- False on the left can always be used.
    apply False.elim h22
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709777028493696592231893884206 : ((((p1 → (p4 ∨ ((p1 ∨ (p5 ∨ p1)) → False))) → ((p4 → ((p1 → True) ∨ p4)) ∧ (False ∨ ((p5 → False) ∨ (p3 → (p3 ∨ p4)))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734713937741260964447544819137 : ((((p1 ∨ p5) ∧ (p1 ∨ ((((p3 → ((p2 ∧ p1) ∧ (p1 → True))) ∧ ((True → True) ∧ False)) ∨ ((p4 ∨ (p4 ∨ False)) ∧ p3)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350271875150190878864157599848 : (p4 → ((p4 ∧ ((p5 → ((p1 ∨ (False ∧ (((True ∨ p1) ∧ (p2 ∨ p2)) ∧ ((p4 ∨ p1) ∧ p2)))) ∨ p3)) ∧ (p4 → (p5 ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342302882603822970022315476710 : (p2 → ((True → ((p3 ∧ (False ∨ ((False ∧ ((False ∧ p2) ∨ (False ∨ False))) ∧ p2))) ∨ (False → p3))) ∨ (((p5 → p3) ∧ p4) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41035596220027410994503905765 : ((((((False → (p1 ∧ False)) ∧ (((((p1 ∧ True) ∨ p5) ∨ p3) ∨ p2) ∨ p3)) ∨ (((True → p1) ∨ p1) ∨ p1)) → (p2 ∧ p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113615601905026995172055073187 : (((p5 ∨ ((p2 ∧ p3) ∧ (p1 → ((((p2 ∧ p4) ∧ (True → p2)) ∨ p4) → ((p4 → (p1 ∨ p3)) → False))))) ∨ (p4 → True)) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805454143478999262826787689438 : (((p3 → (p2 ∨ ((p2 ∧ (p5 ∧ p3)) ∨ ((False ∧ ((((False ∧ (p5 → p3)) → p3) ∧ ((p5 → p3) → (False ∨ p1))) ∧ p3)) ∨ True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637301720470345495019183028419 : ((((((p2 ∧ True) ∧ (p5 ∧ ((p1 ∨ (True ∧ p5)) ∨ (p2 ∧ p3)))) → ((p4 ∨ ((p4 ∨ True) → False)) ∨ ((False ∧ p3) → False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149889982681666787913041873499 : ((p2 ∨ ((False ∨ p4) ∨ (p5 ∧ ((p4 ∧ (p4 ∨ ((False ∧ p1) ∧ (p2 ∨ (False → (p2 → False)))))) ∨ p1)))) ∨ (True ∨ ((p2 ∧ p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743750831918596709772993828757 : ((((True ∧ p4) → (((p4 ∧ (p1 ∨ ((p1 ∨ p1) ∧ ((((False → p1) ∧ p4) ∨ p2) ∧ p3)))) ∧ p1) → (p2 ∨ (p2 ∨ (p5 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149642584298075202429734596487 : ((p4 ∧ ((((p4 ∨ (((False ∨ p1) → False) ∧ p4)) ∨ p4) → ((True ∨ p5) ∧ p1)) ∧ (p4 ∨ (p4 ∧ True)))) ∨ (((p4 ∨ False) ∧ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146779719593618729573705091325 : ((p3 → (((p1 ∨ (p5 → (False ∨ ((p4 → p5) ∧ (p1 ∧ p5))))) → (p3 ∨ p1)) → ((p2 → p5) ∨ p3))) ∧ ((p1 → (p3 → p1)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62361683113099778408293088635 : ((p3 ∧ ((((p2 ∨ False) ∨ (p2 ∧ p1)) → (((p2 → p3) → ((p4 → p2) → p3)) → (p2 → False))) → (((True ∧ True) → True) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609159195138069852035986085160 : (((((((True ∧ p4) ∧ (p5 → False)) ∨ (((p1 ∨ p4) ∨ ((True ∧ p3) ∧ (p2 → True))) ∧ ((False → p4) → (p4 ∨ p4)))) ∨ p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344348421970538828704816334978 : (p2 → (p4 ∨ ((((True → ((p1 ∨ (p5 ∧ True)) ∧ p5)) ∨ False) ∧ ((p3 ∨ (((True ∧ p1) → False) → p1)) → ((False → p2) → False))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327794702775402329447216176033 : (True → ((((p2 → (p3 → False)) → ((((p3 ∨ ((p4 → p5) → (p1 ∨ ((p5 ∧ p4) ∧ True)))) ∧ p2) → False) ∧ p2)) ∧ True) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600074899814215905229007005715 : (((((p3 ∨ True) → (False ∨ ((((((p2 ∨ p2) ∨ p5) ∨ p2) ∧ (p2 ∨ ((p4 ∧ (p4 ∨ p1)) → (p1 ∧ p4)))) ∧ False) ∨ True))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216454499680754758568407696486 : ((p4 → (p1 ∨ (p1 ∧ False))) ∨ (p1 ∨ (p4 ∨ (False → ((p5 → (p2 → ((p1 ∧ (p4 ∧ False)) ∧ ((p5 ∨ False) ∨ p3)))) → (p5 ∧ p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53720717301705658125208607495 : (((p5 ∨ (p4 ∧ (((False → p3) ∨ p1) → (p5 ∨ True)))) ∧ (p5 ∧ (((True → (False → ((p1 ∨ p1) ∨ (p2 → p4)))) ∨ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62127850734382299078086073605 : ((p2 ∧ (p3 ∨ ((False ∨ False) ∧ (p3 ∧ (((((((True ∨ (p5 → (p3 ∨ True))) ∧ (True → False)) → False) ∧ True) ∨ False) → p2) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645929788900910345074991330415 : ((((True → ((p3 ∧ (((((p3 ∨ (p4 → (p3 → (False ∨ ((p4 ∧ p2) ∧ p1))))) → p5) ∨ False) → p1) ∧ p5)) ∧ (p5 → False))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158447116699065908578683727254 : (((p4 ∨ p2) ∨ ((((p5 ∨ (p2 ∨ p4)) ∧ (p5 ∨ p3)) ∨ (False ∧ (p1 ∧ (p5 → True)))) ∧ p5)) ∨ (p4 → (((p3 → True) → p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118752426950296781921693833650 : ((p5 ∨ (((True ∨ p1) ∧ True) → ((True → ((False ∨ p2) ∨ (((True ∨ p1) ∧ (p4 → False)) → p4))) ∧ ((p4 → p2) ∧ False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669472172792395810496210798295 : ((((((p4 ∨ ((((p4 ∨ False) → (p5 ∨ p1)) ∧ (p3 → p3)) → ((True → p3) ∨ p5))) ∧ p5) → (p5 → p3)) ∨ ((p2 ∨ False) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198275220756213342489305408739 : ((False ∧ ((p2 ∨ True) → (p3 ∧ (p2 ∨ p3)))) ∨ ((((p5 ∨ p5) → (False ∨ p1)) → (p2 → ((p3 ∧ (p1 ∧ p3)) ∧ p2))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65818934551606022117600399838 : ((p4 ∨ ((p2 ∨ (((p5 → p1) → p2) ∨ p5)) ∨ (True ∧ (True → ((p2 ∨ p1) ∨ ((((False ∨ p3) ∧ False) → (p4 ∨ True)) ∨ p3)))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257871030475227445653498488885 : ((p4 ∨ True) → ((p1 ∧ ((True ∧ (((p2 ∧ p1) ∧ p3) ∨ p3)) → (((p5 → (False ∨ p2)) → p5) ∨ p1))) ∨ (p5 → ((p4 → p5) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119044991262753596365974639236 : ((p1 → ((((((p5 ∧ (p4 ∨ False)) ∨ (p1 → p1)) ∨ (p3 ∨ ((p4 ∧ p1) ∧ (p2 ∧ (p5 → p5))))) → p3) ∨ True) ∨ True)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651314195530298336269909061862 : ((((((p5 ∧ p3) ∧ p5) ∨ (False → ((p1 → True) ∧ (p2 ∨ (((p4 ∧ p1) ∨ ((True ∧ p3) ∧ p3)) ∧ (p2 → p2)))))) ∧ (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218478166525210163389370729358 : (((True ∨ p5) → (False ∨ p2)) → (((False ∧ p5) ∧ False) ∨ (p2 ∧ ((p5 → (False ∨ ((((p2 ∨ p1) ∧ (p5 ∨ p5)) ∨ p5) ∧ p3))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327752065163368390434153169590 : (True → (((p2 ∧ p3) → (True ∧ ((p3 ∧ ((True ∨ ((p3 ∨ ((p2 → p4) ∧ (p1 ∨ p2))) ∨ p2)) → (p5 → p1))) ∨ p3))) ∧ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49829205602316364580599183465 : (((p3 → (p5 → (p4 → (((False ∧ (((p2 → p2) → False) → p2)) ∧ p4) ∨ (True → ((p5 → p1) ∨ p1)))))) → (p5 → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135986289363941716657778292542 : (((((p5 ∧ p4) → (p5 → (p3 → p1))) → (p2 ∨ p3)) ∨ (p3 → ((p4 → False) ∨ (p1 → (p4 ∨ (p5 ∧ False)))))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349950820916466795234713597875 : (p4 → (((((p1 ∨ p3) ∧ (p2 ∨ ((p4 ∧ True) → (((False ∨ False) ∨ (p1 → False)) ∧ p5)))) ∧ (p3 ∨ (p5 ∨ (False → False)))) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158071607280636696951203108711 : (((((p4 → (p2 → p3)) ∨ p4) → p2) → (((p2 → (False ∨ p2)) → (True ∧ (p4 ∧ p2))) → p4)) ∨ ((p3 ∨ ((p1 ∨ p2) → p1)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (False ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31730907888099566453896623447 : ((False ∨ (((p2 ∨ p4) ∧ (True ∨ (((p2 ∨ p3) → (p2 → p5)) → p1))) → ((p1 ∧ (p1 → p3)) ∨ ((True ∨ (p3 ∨ False)) ∨ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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
theorem thm_5_vars_600105678526559032435082328868 : (((((p4 ∨ p1) → (((p3 ∧ (True → ((True → True) → (p3 ∨ (p3 → ((True ∨ p5) → ((p5 → p2) → False))))))) ∨ p4) → p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338576597249470570897028367402 : (p1 → (((p1 → p5) ∧ p1) → (((((True → True) → (((p1 ∧ True) → p3) ∨ False)) ∧ p4) ∨ p5) ∧ ((p1 ∧ (p4 → p1)) ∨ (p4 ∧ p2))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199792193794221863852017281218 : ((((p3 ∧ (False → p2)) ∧ True) ∧ (p5 → False)) → (((((p5 → p2) → (p2 ∨ False)) ∧ (p3 ∨ ((p5 ∨ (p3 → p5)) → False))) ∧ p5) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353726962368932168737229279063 : (p4 → (True → (((p3 ∧ True) ∨ ((p5 ∧ (p1 ∨ (((((p1 ∧ (True ∨ p5)) ∨ p4) ∧ (p5 ∨ True)) ∧ p4) ∧ p1))) ∧ False)) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624752203698517056792266012019 : ((((p5 ∨ ((((p4 ∨ ((p2 ∨ p5) ∧ ((True → p5) ∨ True))) ∨ (p1 → (p2 ∧ p2))) ∨ (p1 → ((p5 → p1) ∨ p2))) ∧ True)) ∨ p5) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357488183380462810906689856284 : (p5 → (True ∧ (((p3 ∨ (p4 ∧ (((p4 ∧ p5) ∧ ((p2 ∨ ((True → p5) → (p3 ∨ p5))) → True)) ∨ p1))) → (p3 ∧ (False → p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304777145043759353192547698539 : (p1 ∨ ((p4 ∨ ((((p3 → p1) ∨ True) → ((p5 ∨ (p4 ∧ True)) ∨ p5)) ∨ ((p4 ∧ p3) ∨ ((p2 → p4) → (True → False))))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315366793081017770055099538906 : (p3 ∨ ((False ∨ (p4 ∨ True)) ∧ ((((True ∨ (False ∨ p3)) ∨ False) → (((((p4 ∧ p4) → ((p3 ∨ p5) ∨ p2)) ∧ p3) ∨ True) ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_112633949773944642238400317800 : (((((p3 ∨ ((p4 ∨ p1) ∧ ((p5 → (p4 → (p2 ∧ True))) → p2))) → ((False ∧ p4) ∧ (False ∨ False))) → (True ∧ True)) → p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155244146445382074488585169016 : (((((True → False) ∧ True) ∧ ((False → True) ∧ p4)) → ((False ∧ (True ∨ (p4 ∧ (p5 ∧ p2)))) ∧ p1)) ∧ (((False ∧ (False ∨ False)) → p2) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h11.left
  let h15 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h17.left
  let h21 := h17.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h22 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h23 := h18 h22
  -- False on the left can always be used.
  apply False.elim h23
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219537661659286365464987229472 : ((p5 ∨ (True → (p5 ∧ p4))) → (p5 ∨ (((p1 ∨ (False → p2)) → ((True ∨ (False ∧ p3)) ∨ ((p5 → p5) → p5))) → ((p3 ∧ p1) ∧ p5)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136203769181999295022135922241 : (((p1 ∨ ((p5 → (p3 → True)) ∧ True)) ∧ ((p2 ∧ (p3 ∨ p5)) → (p4 ∨ (((p3 → True) → False) ∧ (p1 ∨ p1))))) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124320292455118957639060197099 : ((((p5 → p4) → (False ∧ (p4 ∧ (p1 → p2)))) ∧ ((p5 ∧ (((True ∨ p4) ∨ (True ∨ (p3 ∨ p1))) ∨ (p4 ∨ p4))) ∨ p5)) → (p2 → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h16 =>
            -- One of the premise coincides with the conclusion.
            exact h2
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726271666479950167994994819592 : (((((p1 ∨ p3) ∨ p1) ∨ ((((((p5 → True) ∧ True) ∨ True) → p3) → ((False ∧ p1) ∨ (p2 ∧ (False ∧ ((p5 ∨ True) → p3))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180763909656481931037272967184 : (((((p2 ∧ False) ∨ p3) ∧ True) → ((p5 → p2) → (p4 → (False ∧ False)))) → (((False → (False → False)) → p2) ∨ (True ∨ (p3 → (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177932265577448405341230745537 : ((((False ∧ (False ∧ (p4 ∧ p3))) ∨ ((p5 → p4) → (p3 → p5))) ∨ True) ∨ (True ∧ ((((p4 → (p3 ∨ p4)) → False) ∧ (True ∨ True)) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352033253226119731255441266273 : (p4 → (((p5 → (p3 → (p1 ∨ False))) ∨ (p2 ∨ p2)) → (p4 → (p5 ∨ (p3 ∨ ((True ∨ True) ∨ (((p2 ∨ p1) ∨ (p2 → p1)) → p3))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
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
theorem thm_5_vars_4278178617405065054278164975 : (True → ((((p5 ∧ p4) → ((p1 → (True → p4)) ∧ (((p3 → True) → (True → (p1 → p4))) → (p1 ∨ False)))) ∨ True) ∨ (False ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



