variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253718725404503111603471182289 : ((p1 ∧ p1) → ((((p1 ∨ p3) → (((p1 ∧ (p4 ∨ (p4 → True))) ∨ p5) → p5)) ∨ ((p3 ∨ ((p4 ∨ p3) ∧ p5)) → (p3 ∨ p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149158734067268417595694834968 : (((p2 ∨ p3) ∧ (True → (p2 → ((False ∧ (False → (p4 → False))) ∨ (False ∧ (p2 → ((True → p3) ∧ p3))))))) ∨ (True ∨ (p1 ∨ (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655811481322206395680183566751 : (((((p3 → ((p1 → (p2 ∨ p5)) ∧ (((p4 → True) ∨ p1) → (((p1 → False) ∧ False) ∧ p1)))) ∨ (p5 → (p5 → True))) ∨ (False ∧ p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165078077333415501939362596001 : (((True ∨ (((p3 ∨ (False ∨ ((p1 ∧ p5) → (p1 ∨ p5)))) ∨ (p3 ∨ p1)) ∨ True)) → p5) ∨ ((p3 ∨ ((p4 → p4) ∧ p3)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156782223134142705655270006867 : (((False ∧ ((p3 ∧ ((p1 ∨ p2) ∧ ((p5 ∧ (True → False)) ∨ (p5 ∨ p5)))) ∨ (p3 ∧ p2))) ∧ p2) ∨ (((p5 ∧ True) ∨ (False ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_310313591622288538708180566336 : (p2 ∨ ((p4 ∨ ((((p3 ∨ p2) ∨ p3) ∧ True) ∨ (p2 → True))) ∨ ((p1 ∨ (p3 ∨ (p3 ∨ True))) ∧ (((p3 ∧ p1) ∨ p5) → (p4 ∨ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65816266190353513736127452564 : ((p4 ∨ (((p1 ∧ ((p4 ∧ p3) ∨ p1)) ∧ p5) ∨ ((True → (True ∨ (((p5 → (True → (p2 ∧ (p1 → False)))) ∧ p4) ∨ p4))) ∨ p1))) ∨ p1) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112837884605126559566604410246 : ((((True ∧ ((p3 → p1) → p2)) → ((p2 → ((((p3 ∨ (p1 → p4)) ∨ (p1 → (p5 ∨ p5))) → p5) → p1)) ∨ p2)) → p4) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356521355640462626707882650672 : (p5 → (((((p3 → p5) ∧ (p4 ∧ (p4 ∧ p3))) ∧ p5) ∨ False) ∨ (((p2 ∧ False) ∧ (((p5 ∨ p1) → p5) ∨ p3)) ∨ ((True → p5) → p5)))) := by
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
theorem thm_5_vars_40507688541848537781790782421 : ((((p2 ∧ (((True ∧ (p1 ∨ ((p5 ∧ p3) → ((False → ((True ∧ p1) ∨ p2)) → p3)))) → (p2 ∨ p1)) ∧ (p5 ∨ True))) ∨ p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173180594625516102532743794308 : ((p4 ∨ ((((p3 ∧ p4) → p5) ∨ False) → ((p4 → p5) ∧ ((p1 ∨ p4) ∨ p1)))) ∨ ((p4 → p2) ∨ (p3 → (False ∨ ((p3 → p5) → True))))) := by
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
theorem thm_5_vars_171630296142881121519655096918 : ((((False ∧ True) ∧ (p4 → ((p3 ∨ p1) ∨ (((p4 ∧ p4) ∧ p4) ∧ p2)))) ∨ p3) ∨ ((((p5 → True) ∨ (True ∨ p3)) ∨ (p1 ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659259434374721260277131353622 : ((((p4 → (p1 ∨ (p2 ∨ (((((p4 ∨ (False → p4)) ∧ (((p3 → True) → p2) ∧ (True → p1))) ∧ p2) ∧ True) ∧ p4)))) ∨ (True → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_184488471318100203069828910673 : (((((False ∧ False) → (p4 ∨ True)) ∧ (True ∧ p5)) ∨ (p5 ∨ p3)) ∨ (p3 ∨ ((p4 → False) ∨ (p4 → ((p3 → (p4 ∨ (p1 ∧ p4))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337115550108476768839170065811 : (p1 → (((p4 → p5) ∨ (True → (True ∧ ((p5 ∨ p2) ∧ ((p5 → (True → ((((p1 → p1) ∨ p2) → p3) → p2))) ∧ False))))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358584526723857345512567947397 : (p5 → (p3 → ((p3 → (p4 → (p4 ∧ (((p3 ∨ (p1 → ((p3 ∨ ((True ∧ p4) ∨ (p2 ∨ False))) ∧ (True ∧ p3)))) ∧ p4) → p2)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152324354819828495571540415268 : ((((False → p1) → (p3 ∨ p2)) ∧ ((((p4 → ((p2 ∨ p1) ∧ True)) ∧ (p4 ∧ p3)) ∨ (p2 ∧ p2)) → p1)) → ((p3 ∧ (True → p4)) ∨ True)) := by
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
theorem thm_5_vars_350909601824787962499209340173 : (p4 → ((((p4 → (False ∨ p3)) ∧ (p2 ∨ (False ∧ ((p2 ∨ (((True ∧ (p3 → (p1 ∧ p1))) ∧ p3) → False)) → False)))) ∧ p5) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165309156063730361419427503673 : (((p5 ∧ (p2 ∨ (((p2 ∨ p3) ∧ ((False ∨ p3) → (p3 ∨ True))) ∨ p4))) → (p4 → p1)) ∨ ((p1 → p5) ∨ (((p2 ∨ False) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193199565174381556312866103137 : (((p1 ∧ ((p2 ∨ False) ∧ p2)) → ((True ∨ p4) ∧ p1)) → (p4 ∨ (((p4 ∨ ((True → p5) ∧ ((False ∧ p1) ∧ (p3 ∧ p5)))) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310796782010827427950865417488 : (p2 ∨ ((True ∧ (p4 ∧ p1)) ∨ (p1 ∨ (((p3 ∨ p3) → p3) ∧ ((p2 → ((p2 → p3) ∨ ((p4 → p1) ∨ (p5 → (p1 → p1))))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300103643837623532715897865668 : (False ∨ ((((p3 → (p5 ∨ ((p2 ∨ p4) ∨ p3))) ∧ (((p3 ∧ p3) → p2) → False)) → (p3 ∧ (False → ((p3 ∨ p1) ∧ p2)))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156566394645873141740606266422 : ((p5 → (((((p4 → ((p2 ∧ p3) ∨ True)) ∨ p1) → p1) ∧ ((p3 ∧ p2) ∧ p4)) ∨ (p2 → True))) ∧ (True ∨ (p5 ∨ ((p5 → p2) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337347274393314681937795193215 : (p1 → (((p4 ∧ (p1 → (((p4 ∨ False) ∧ (p1 ∧ ((p2 ∨ False) ∨ (p1 ∧ (p2 ∧ p5))))) ∨ (p5 ∧ p2)))) ∨ p2) ∨ (False → (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265717975179944594943509170787 : (True ∧ (p3 ∨ (((p1 ∧ (p5 ∨ False)) ∨ ((p3 ∧ p5) → (p4 ∨ p3))) ∧ ((p4 ∧ ((p1 ∧ (p2 ∧ (False ∧ p2))) → (p4 ∨ p3))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305438638916919310405787532453 : (p1 ∨ ((((True → (p2 → p1)) ∨ (p2 ∨ (p3 ∨ False))) ∧ (True → ((p3 ∧ p4) ∧ False))) → (p2 ∧ (True ∧ (p4 ∨ (p1 ∨ (p1 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h25 := h17 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h30 := h17 h29
        -- We need to get the right conjuct of h30 based on <expert-advice>.
        let h31 := h30.right
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357091832387577887837185708864 : (p5 → (((p3 → p4) → p4) → (((p4 ∧ (((p3 → (False ∨ p3)) → p3) ∨ p5)) → (p3 → (((p2 → p1) ∧ (True ∧ p4)) ∨ False))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686487681746092900311263228176 : (((((p3 ∧ (p2 ∧ True)) ∨ (p4 ∨ ((False ∨ p4) ∨ ((p1 ∨ ((p3 ∨ False) ∧ True)) → True)))) → ((p3 ∧ p4) ∨ ((p3 ∧ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678822707668343081130509515839 : ((((False ∧ ((((p1 ∨ (((p1 ∨ p1) ∨ p1) ∨ p1)) ∧ True) → (p2 ∧ False)) ∧ ((p5 ∧ p5) ∧ p3))) ∨ (((p4 → p4) ∧ False) → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300377922305209259658100490264 : (False ∨ (((((True ∨ ((p1 → (p2 → p4)) ∨ ((p3 → (p2 → p1)) → p1))) ∨ False) ∨ p2) → ((p3 ∧ p3) → False)) ∨ ((p2 → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150019022227670776458266672294 : ((p5 ∨ (((p3 ∧ ((p2 → False) ∧ ((True ∧ (False ∨ False)) → p1))) → p1) ∨ (True ∧ (p2 ∨ (p2 ∧ p2))))) ∨ (((p1 ∧ p5) ∧ p5) → p1)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351646568767950895121193946799 : (p4 → ((p2 ∧ ((((((p2 ∨ True) → p2) ∧ p2) → ((p2 ∧ p5) ∨ False)) ∨ p1) ∨ p4)) ∨ ((False → (p4 → (True ∨ (False ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345055725000992074176471063126 : (p3 → (((True → (((True → ((p4 ∧ (True → (p4 ∨ (True ∨ p3)))) ∨ ((False ∧ p3) ∧ p3))) ∨ True) ∧ False)) → (p5 ∨ (p4 ∨ p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51512995263178743629164065119 : ((((p1 ∨ p1) ∧ (((((p1 → p5) ∧ p5) ∨ p1) ∧ ((p1 → True) ∨ (False ∨ p5))) → False)) → (True ∧ (((p5 → p3) → False) ∧ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((((p1 → p5) ∧ p5) ∨ p1) ∧ ((p1 → True) ∨ (False ∨ p5))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : ((((p1 → p5) ∧ p5) ∨ p1) ∧ ((p1 → True) ∨ (False ∨ p5))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h10
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : ((((p1 → p5) ∧ p5) ∨ p1) ∧ ((p1 → True) ∨ (False ∨ p5))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h16
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : ((((p1 → p5) ∧ p5) ∨ p1) ∧ ((p1 → True) ∨ (False ∨ p5))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h22 := h14 h20
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51205138214595958666912951175 : ((((p1 ∧ (((False ∨ p2) ∧ p5) → (p1 → (p4 → p1)))) → ((p1 ∧ True) ∧ (p5 ∧ False))) ∨ ((False ∨ ((p3 ∧ p5) ∨ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612892846664197113925694125384 : (((((False ∨ (p5 ∧ (((False → p1) → (p3 ∨ ((p1 ∧ p4) ∨ p4))) ∧ ((p2 → (p1 → p3)) ∧ (True ∧ p1))))) ∨ (p1 ∨ p1)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353760030328401784375328708502 : (p4 → (True → (p2 ∨ (False ∨ ((False ∨ p2) ∨ (p1 ∨ (((True → p1) ∧ (((((p2 → (True → p4)) ∧ True) ∨ p3) ∧ False) → True)) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263738374511573373265067274361 : (True ∧ (((p1 ∨ p4) ∧ ((((p5 ∨ p5) → p5) → (p1 ∨ (((p1 ∨ True) ∨ p3) ∨ p3))) ∨ True)) → (False ∨ (((False ∧ p2) ∧ p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114402322356921387168345459024 : ((((p3 ∧ (p4 ∨ ((p3 ∨ (p2 → True)) → p4))) → ((False ∧ False) ∧ (False → (p2 → True)))) ∨ ((False → (p1 ∨ p1)) ∨ p4)) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227785917646528993720736405386 : ((p1 ∧ (p2 → p3)) ∨ ((False → (p5 ∧ p1)) ∧ ((True → (p4 → (p2 ∧ (False → p4)))) ∨ ((False ∨ (p3 → p2)) ∨ (p1 → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_111099248666006918364331995602 : ((((p3 → (False → ((p1 → p4) → (p4 → ((False ∨ p1) ∧ False))))) → (((p2 ∧ (True ∧ (p5 ∧ p5))) ∧ p5) → False)) ∧ p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52464846049474973651117891471 : (((p1 ∨ ((((p4 ∧ p5) ∨ p1) ∨ p3) ∨ (((False ∨ False) ∨ p5) ∧ True))) ∧ (((True ∧ p1) ∧ p5) ∨ (p4 → (p1 → (p5 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184795474177860631588064639911 : ((((p4 → True) → (p4 ∧ p1)) ∨ (False → ((p5 ∧ True) → p5))) ∨ (((False ∧ p2) → False) ∨ (((p3 → (p4 ∧ (p3 ∨ True))) → p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806260631519043483666537204733 : (((p4 → (((p4 ∧ ((True ∧ True) ∧ (p2 ∨ (True ∧ ((True ∨ p1) → (p1 ∨ p5)))))) ∧ (((p3 → (p3 ∨ p2)) ∧ p2) ∨ True)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667817718426707047134586316134 : ((((False ∨ (((True ∧ (p4 ∨ ((p3 ∨ ((p2 ∨ p2) → p1)) ∧ (p2 ∧ False)))) ∨ ((False ∧ p3) → False)) → p5)) ∧ (p2 ∨ (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82222873947496388548708746097 : (((((p1 ∨ p2) ∧ ((p5 ∧ (((p5 ∨ False) ∨ ((p3 → p4) → (p5 → p4))) → p1)) ∨ p3)) ∧ p2) ∧ ((True ∨ p2) ∧ (p3 → False))) → p1) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h28 : ((p5 ∨ False) ∨ ((p3 → p4) → (p5 → p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h29 := h24 h28
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h31 : ((p5 ∨ False) ∨ ((p3 → p4) → (p5 → p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h32 := h24 h31
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h3.left
      let h35 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h37 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h38 := h35 h37
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h40 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h41 := h35 h40
        -- False on the left can always be used.
        apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137162233512914055371918742567 : ((False ∧ ((((((p4 → p4) → (p2 ∨ p3)) ∨ (False ∧ p3)) ∨ (True ∧ p2)) → ((p4 ∧ (p3 → p4)) ∨ p3)) → p3)) ∨ (True ∧ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54840931068663287578063389444 : (((p4 → (p4 ∧ (p2 → ((p3 ∧ p5) ∧ p3)))) → ((p5 → ((((p1 ∧ False) ∧ p3) ∨ (p1 ∨ p2)) ∨ False)) ∨ (False → (p2 ∧ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591852093912844449866705533716 : ((((((((p4 ∨ p2) → ((p2 → False) ∨ (p4 ∧ (p1 → True)))) ∨ p5) ∧ (((True → p5) → (p5 ∧ True)) ∧ False)) ∨ (p1 → p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55564258703498627797924130397 : (((p5 ∧ (((False ∨ True) ∧ p2) ∨ p1)) → (((((p5 ∧ False) ∧ (((p4 → p2) → p3) → p3)) ∨ p1) ∧ (p1 → p5)) ∨ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336211440260148974239413955507 : (p1 → ((((((p5 ∧ (p4 ∨ p4)) ∨ p1) ∨ p2) ∧ (((p4 ∧ ((p3 ∧ p3) ∧ (False → False))) ∨ (p5 ∧ p4)) ∨ p4)) → (p5 ∨ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161310945994639461243504971256 : ((True ∧ ((p4 ∧ ((p3 → (((p3 ∧ p5) ∨ True) ∨ ((p4 ∨ True) → (p3 → p2)))) ∨ True)) → True)) → ((p2 ∨ (p5 ∧ (p4 ∨ p4))) ∨ True)) := by
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
theorem thm_5_vars_135508071396333868440152664014 : (((p5 ∨ (False → ((((p4 → p1) → (p1 ∧ p2)) ∨ (p5 ∧ False)) → ((p5 → p4) ∨ p3)))) → (p3 ∧ (p5 → False))) ∨ (p1 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115105436576432537772932773791 : (((((p3 → ((False ∨ p4) → (True ∨ False))) ∨ (p2 ∧ p5)) ∨ p4) → (p5 ∧ ((True ∨ p2) ∧ (p5 ∨ (p4 → (False → True)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338409102102388179234102510527 : (p1 → (((p3 ∨ False) ∧ (p5 ∨ p2)) → ((p2 ∨ ((p3 ∧ (False ∧ (p4 ∧ p4))) ∧ (p2 → ((True → p1) ∧ p4)))) ∨ ((p2 → p1) ∨ p5)))) := by
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
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156938371306933358688991024039 : (((((p1 ∨ ((p2 ∨ (p3 ∧ p5)) → (p2 ∨ ((p2 → p1) ∨ True)))) → p2) ∨ (p2 ∨ p5)) ∨ p1) ∨ ((p3 → False) ∨ (p2 → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670548455702176005763818529947 : (((((p4 ∧ p3) ∨ (p5 → (((p4 ∨ p2) → ((p3 ∨ (p1 → (p5 ∨ p2))) ∧ True)) ∧ ((True → p2) ∧ True)))) ∨ (p2 → (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119530285024041011569829054164 : ((p5 → ((((((((p4 ∧ (p5 → p1)) → p1) → ((p4 ∧ p2) ∨ False)) ∨ p3) ∧ p4) → (p4 → True)) ∧ (False → p4)) → False)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317792355153306239557946258342 : (p4 ∨ (((((True ∨ p4) ∧ ((p3 ∧ (p3 → p3)) ∧ p4)) ∨ p1) → ((((p2 ∧ p1) → p4) ∨ p4) ∧ ((p1 ∨ p5) ∧ (p2 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299116939671255919251777829909 : (False ∨ (((True → ((p3 ∧ ((p2 ∧ (((p2 → ((p5 ∨ p5) ∨ True)) ∨ True) ∨ False)) → (True → ((False ∨ p2) ∨ p2)))) → p4)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111076752014336050644475728078 : (((((p1 ∧ p5) ∨ ((False → False) ∨ (p2 → (p3 → (False ∧ (p1 → p3)))))) → (((p1 ∧ (p2 ∨ True)) ∨ p5) ∧ p5)) ∧ p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49867818762825981075128520466 : ((((p1 ∨ (((False → (((False → p5) → p3) → p1)) → (p1 ∧ (p1 ∧ p5))) → (False ∨ p5))) ∧ p3) ∧ (((False ∧ p2) ∧ p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86728837881027338284248681409 : (((True → (((p1 → p4) → p4) → (False ∧ True))) ∧ (p4 ∧ ((False → ((False ∧ ((p3 ∧ (p1 ∧ False)) → p3)) ∧ (p4 ∧ p3))) ∧ True))) → p2) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p1 → p4) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248712542580878894379276635689 : ((p3 ∨ p2) ∨ ((True ∨ (p4 ∧ p5)) ∧ ((((p2 ∧ p2) ∧ (p4 ∧ p2)) → ((((p3 ∨ p1) ∧ p3) ∨ p5) ∧ (p5 ∨ (p5 → False)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305160866915231074421355012382 : (p1 ∨ ((((p4 ∧ (p4 ∨ p2)) ∨ (p2 ∧ ((((False ∨ True) ∧ ((p5 → p2) ∧ True)) → p5) ∨ p5))) ∨ False) ∨ (p4 ∨ ((p5 ∧ False) → p1)))) := by
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
theorem thm_5_vars_350179811459341993157342592656 : (p4 → (((p5 ∧ (p2 → (p4 ∨ p3))) ∧ ((p1 → ((((False → p4) → p2) ∨ p5) ∧ p3)) → (((True ∨ (p1 → p4)) ∧ False) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338775004133520407957372644789 : (p1 → ((p3 ∧ True) ∨ ((p1 → p5) → (((True → (p2 ∧ p3)) ∧ (((True → p2) ∨ p3) ∧ p4)) ∨ (p5 → (((False ∧ True) ∧ p4) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68011981525118438549404717013 : ((p2 → ((p2 → p2) → ((p1 ∧ (((p3 ∧ p1) → p3) → (((p4 ∨ ((p2 ∧ False) ∨ (p2 ∨ True))) → (p2 → p1)) ∨ p1))) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118621601809034599835229270063 : ((p4 ∨ ((p4 ∨ (p5 → (True → (True ∨ (p2 ∨ p2))))) ∧ ((p1 ∨ ((p1 ∧ p3) ∧ (((p2 → p2) ∨ False) → p2))) ∧ p1))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228049789786342382449902595851 : ((p4 ∧ (False ∧ p3)) ∨ ((p5 → ((p4 ∧ ((True → p3) → (p1 ∨ p4))) ∨ (((p1 ∧ ((p5 ∧ p2) ∧ False)) ∨ p2) ∨ (p3 ∨ p5)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232044457468008051530308202691 : (((p3 ∨ p3) → p5) → (p5 ∨ (((p5 ∧ p4) → (((False ∨ ((p3 ∨ (p2 ∨ False)) ∨ p2)) ∨ True) ∨ (p3 ∨ (True → True)))) ∨ (p5 → True)))) := by
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
theorem thm_5_vars_306512795553766803347301798148 : (p1 ∨ ((True ∧ p4) → ((((p5 ∨ False) ∨ ((((True → p1) ∨ (True ∨ p3)) ∧ (False → p1)) ∧ (p2 ∨ (p3 → (p1 ∧ p1))))) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733938580333147689150180392093 : ((((True ∨ False) ∧ ((((p5 → ((False ∧ False) ∧ p5)) ∨ p3) ∨ ((p1 ∨ ((((p5 ∧ p4) ∧ False) ∧ (p3 → p1)) ∨ p1)) ∨ False)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208578373264867383197111989699 : (((False → False) → ((p2 ∨ False) ∧ p3)) → (((p2 ∨ ((p1 → False) ∧ (((p1 ∧ False) ∨ True) → False))) → (((p1 ∨ p3) ∨ False) ∧ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253741505094871901710875372664 : ((p1 ∧ p1) → ((p5 ∨ (((p4 → (p2 → (p5 → p2))) ∧ ((p3 ∧ p1) → (p4 ∧ (p4 ∧ p1)))) ∨ p2)) ∨ (p5 ∨ ((True → True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139235318562369091082215132620 : ((((p5 ∨ p4) ∧ (((False ∧ p3) ∨ ((p1 → p2) ∨ (((True → p1) ∧ p2) → (True ∨ p4)))) → (p3 → p2))) ∨ p4) → (p2 → (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40715481784580891391799338296 : (((((True ∨ ((((False → p1) ∨ True) → p1) → p3)) ∧ ((p1 ∧ p4) ∧ (True ∧ (p2 ∧ (p3 → (False → (True ∨ p5))))))) → p1) ∨ p3) ∨ p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h15.left
    let h19 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147983597980210160361352416256 : ((((True → ((((True ∧ (p2 → True)) → (((p3 → p3) → False) → p1)) ∨ p1) → p3)) ∧ True) ∨ (p1 ∨ p5)) ∨ (p4 ∨ ((p1 → p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674457520945885861613447093957 : ((((p3 ∨ (p4 ∨ ((p1 → (((((p4 → p1) ∧ p5) ∧ (p4 ∨ ((p2 ∧ p1) ∧ p4))) ∨ p3) → False)) → False))) → (p2 ∨ (p4 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221735703858609706903400664270 : (((False ∧ p4) → p3) ∧ (p1 → ((((True → ((True → (p1 → (p3 → (p1 → (p3 → p2))))) ∧ False)) ∧ True) ∨ ((p4 ∧ p4) ∨ p4)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_373565070739471178198785610904 : (((((p3 ∨ p5) → (((p2 → (p5 → (((p2 → p3) → ((p5 ∨ p1) ∨ p1)) → (p3 → p2)))) ∧ (p2 ∨ (False ∧ False))) ∨ True)) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57082645331294420311025604530 : ((((p1 ∧ False) ∧ p3) ∨ (p1 → ((((True ∨ (True → (True ∧ (p3 ∨ False)))) ∧ ((((p5 ∧ p4) → False) ∧ p1) ∧ p5)) ∨ p5) ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_303224756225452310671467445358 : (False ∨ (p5 → (((((p3 ∨ p1) ∧ ((True ∧ p2) ∨ p5)) ∨ ((False ∧ p3) ∧ ((p2 → False) → ((p5 ∧ p2) → (True → p4))))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158907073788555928739970141242 : ((p1 ∨ (((p5 → ((p5 ∨ ((p1 ∧ True) → True)) ∨ p1)) ∧ p1) → ((p2 ∨ False) ∧ (p1 ∨ p5)))) ∨ ((p4 → False) → (False → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115533997504531488371253755265 : (((p5 ∧ (p5 ∨ ((p3 ∧ False) → (p5 ∧ p4)))) → (p5 → (p1 ∨ ((True ∧ ((((p4 ∨ p2) ∨ p5) ∨ p5) → p2)) ∨ p4)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51647432685007953323697016857 : ((((p4 ∧ (False ∨ (p5 ∧ (((p3 → p3) → (p4 → (p1 ∨ True))) → p5)))) ∨ True) ∧ ((True → ((p2 ∨ p1) → (p4 ∨ p5))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147374662875915926224045925443 : (((((p4 ∧ p4) ∧ (((p1 ∨ ((p4 → p5) ∧ p3)) → p4) → p2)) → ((p5 → (p2 → False)) ∧ p4)) ∨ True) ∨ (p1 ∨ (p2 → (p2 ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261377556762724863528736196059 : ((p5 → p1) → (((True ∨ p2) → ((((p5 → p3) ∧ False) → p1) ∧ ((p3 → (p2 → ((p3 ∧ (True ∧ p1)) ∨ p4))) → (p5 ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207951515146872654142026082519 : (((p3 → (False ∧ True)) ∧ (True → True)) → ((p3 → p1) ∧ (((p1 ∧ (True ∨ False)) ∧ ((p4 ∧ True) → ((p1 ∧ p5) ∧ (p2 ∨ p5)))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41644439428836105038238896597 : (((((p3 ∧ ((False ∨ p5) ∨ p1)) ∨ p5) ∧ (((((True ∨ (p1 ∨ (False ∨ False))) → p2) ∧ ((p3 ∨ p2) → p1)) → p2) → p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174656754260765222373837973442 : ((((True ∨ p5) → False) ∧ (((((p2 → p1) ∧ p3) → p5) → p5) ∨ (p3 ∧ p3))) → (((((p3 ∧ p3) → (False ∨ p4)) → p4) → p2) → False)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151797658900075081526761485718 : (((((p1 ∨ (p4 ∧ (((p1 → p4) → p3) ∨ p1))) ∧ (p2 → p5)) ∧ p2) ∧ (p4 ∨ (p4 ∨ (True ∧ False)))) → (False ∨ (p2 ∨ (p5 → p3)))) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- False on the left can always be used.
          apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136437872582445635936973389763 : ((((True → p5) ∨ (True → p3)) → (p1 → (p2 ∨ (False ∧ (((p5 ∨ (False ∨ (p5 ∧ p4))) → False) → (False ∨ p3)))))) ∨ (p2 → (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754096493372567232606284848086 : (((False ∧ (((p1 ∨ False) ∨ False) ∧ ((p4 → p3) → ((((p4 ∨ (p3 → p1)) ∨ (False → p4)) ∨ (p3 → (False → True))) ∨ (False → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197409130274891131747668889490 : (((p1 → ((p3 ∧ (p1 ∨ p3)) → p2)) → p5) ∨ (p1 → ((p1 ∨ ((True ∧ p3) ∨ p5)) ∨ ((True → (p1 → (p5 → p4))) → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197642775386470248028856806747 : (((((p3 ∨ p2) ∧ p5) → True) → (p4 → False)) ∨ (((False ∧ (p2 → (p1 → p2))) → ((True ∨ p4) ∨ (True ∧ ((p5 ∨ False) → True)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102695570879182911461360030285 : ((((((True ∨ p1) → ((((True ∨ False) ∨ p1) → (p3 ∨ p1)) ∧ (p1 ∧ ((p3 ∨ p5) ∧ p4)))) ∧ (p1 ∨ p2)) ∨ True) ∨ p2) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622786005268674144823031924566 : ((((p4 ∧ (p5 ∨ (p4 ∧ (((((True ∨ False) ∧ (p2 ∧ p5)) ∧ ((True ∨ p5) ∨ (True ∨ (p5 ∨ True)))) ∧ (p5 ∨ True)) ∨ p4)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_747070371204959127574839006668 : ((((p4 ∨ p4) → (p2 ∧ ((p2 ∧ (p1 ∨ (((p1 ∧ p3) ∨ ((p5 ∨ p4) ∨ (((False ∨ p1) ∧ (p4 ∧ p3)) ∧ p5))) ∧ p3))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198177772607616567644385844438 : (((p4 ∨ p3) → (p4 ∨ (False ∨ (p4 ∧ p3)))) ∨ ((((p4 ∨ p4) ∧ (p1 ∨ (False ∨ p1))) ∨ True) ∨ (p1 ∨ (p3 ∧ (p3 → (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



