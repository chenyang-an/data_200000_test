variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727367192271099809789878858795 : ((((p2 ∧ (False ∨ p2)) ∨ ((p4 ∨ p4) ∧ ((p2 → ((((False → p5) ∧ (p1 ∨ (((p5 → p1) ∧ p5) ∨ True))) ∨ p2) ∨ p3)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708031136656896810409315875974 : ((((p2 ∨ (p2 ∧ (((p5 → p2) ∨ False) ∨ True))) ∨ ((((p4 → (((False ∨ (p5 ∨ p5)) ∧ (p3 ∧ p3)) ∧ p2)) ∧ True) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743740353918599457854853576052 : ((((True ∧ p4) → ((True ∧ (((((p3 ∨ p5) ∧ p4) → p1) ∨ (((True ∧ True) ∧ (p5 ∧ True)) → p1)) → ((p5 ∧ p2) ∨ p3))) ∨ True)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687979499061934865646833096684 : (((((p2 → (p3 ∨ (p3 → (False ∧ (True ∧ p5))))) → (p5 ∧ (False → (True → p5)))) ∧ ((((p3 ∧ p5) → True) ∧ (p2 ∨ p5)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656796577436744286549516426232 : ((((((True ∨ p3) ∨ (p5 ∨ (False ∨ p1))) → ((p2 ∧ p4) ∧ ((p3 ∧ (p5 ∧ (False → p4))) ∨ (True ∨ (p2 ∨ p3))))) ∨ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157737731968784654509296420212 : ((((((((p3 ∨ p4) → p5) → True) ∧ (p1 ∧ False)) ∨ p2) ∧ False) ∧ ((p4 → True) ∧ (False ∨ p2))) ∨ (((p2 → True) → (p4 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206618488205955215067063242602 : ((p1 → ((False ∧ (p4 ∨ p1)) ∧ False)) ∨ ((((((((p1 → p3) → p4) → p5) ∨ p3) ∨ p4) ∧ p3) ∧ p3) → (((p4 ∨ p1) ∨ p5) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163479232975145343715626415213 : ((((p2 ∧ True) ∧ p2) ∨ (((p2 ∧ (((p2 → p2) ∧ p1) → False)) → (True → p1)) ∨ True)) ∧ (((((False ∨ p4) ∨ p2) → False) → False) ∨ True)) := by
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
theorem thm_5_vars_217498038479848964808353315935 : ((((False ∨ p5) ∧ p3) → p4) → ((((True → (p2 ∨ False)) → (p1 ∨ p3)) ∧ ((((p5 → p2) ∧ False) ∧ p4) ∨ p1)) ∨ (p5 ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_783212267644841476932172398261 : (((p3 ∨ (((((p3 ∧ ((True ∨ p1) → p3)) ∨ (p4 ∨ p5)) ∨ (False ∧ (True ∨ ((p4 ∨ p4) ∧ True)))) → p4) → (True → (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148345083041856849258519518129 : ((((False → ((p3 ∧ p1) → False)) ∧ (((p1 ∨ (p2 ∨ p1)) ∧ p4) ∨ p1)) ∧ (False ∨ ((False ∧ p2) ∨ p1))) ∨ (((p5 ∧ False) ∧ p2) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198374828069405586375028492019 : ((p3 ∧ (((True → (True ∧ False)) → p3) → p5)) ∨ ((p2 → ((p1 ∨ True) ∧ (((True → (True ∧ True)) → (p1 → p4)) ∨ (False → False)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323827958781477079910288759008 : (p5 ∨ (((p2 ∨ ((((((p2 → True) ∨ p5) ∨ p3) ∧ (p2 → p5)) ∨ False) ∨ True)) → (p4 ∧ p2)) → ((p2 ∨ (p3 ∨ p4)) ∨ (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((((((p2 → True) ∨ p5) ∨ p3) ∧ (p2 → p5)) ∨ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136849106791764473136353564934 : (((p3 ∧ p4) ∨ ((p1 ∨ ((False ∧ p5) ∨ p2)) ∨ (p4 ∧ ((p4 ∨ ((p2 → p5) → (p5 ∨ (p4 ∨ p4)))) ∧ True)))) ∨ ((False ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353993884315419220596257144643 : (p4 → (p3 → ((p1 → False) → ((((p3 → (((p4 → p5) ∨ p2) ∨ p4)) → (False ∧ p1)) ∧ ((False → p3) ∨ (p1 ∨ False))) → (p5 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45323029712958592359628512943 : (((p3 ∧ (((p5 ∨ (p5 ∨ ((((p4 ∧ p5) ∨ p1) → True) ∧ p1))) → False) → ((p2 ∧ p4) ∨ ((p4 ∨ True) ∨ (True ∨ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110917752996081849385675794204 : ((((p3 ∨ (True ∨ ((((p4 → p5) ∨ (False ∨ ((p3 ∧ p4) ∨ False))) ∨ (False ∨ (p4 → (p3 ∨ p4)))) ∧ p1))) → p4) ∧ True) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324700498453982656232049253687 : (p5 ∨ (((p2 ∧ p3) ∧ p2) → (p5 ∨ (((p1 → p5) ∨ True) → ((p1 → False) → (((p4 ∨ ((True ∨ p3) ∧ (p1 ∨ p2))) ∧ p1) ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784954886092323221981627846743 : (((p3 ∨ (p4 → (((((False ∨ (True ∧ ((p4 → False) ∨ ((p3 → p1) → p5)))) ∨ (p5 → (p3 → p1))) ∨ False) ∨ (p1 ∨ p5)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161572801041002903079700605410 : ((True ∨ ((p1 ∨ (((p3 ∧ True) → (p3 → False)) ∨ (((p3 → (True ∧ p3)) → p3) ∧ p3))) → p4)) → (p4 → (((p5 ∧ p5) ∨ p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114861363810713831759872099992 : (((((p3 ∨ (((False ∨ (True ∧ p2)) ∨ p1) ∨ p1)) ∨ p4) → (p1 ∨ p1)) ∨ ((((p2 ∧ p2) ∧ p4) ∧ (True ∧ p3)) → p3)) ∨ (False ∧ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801894045777927369101707615155 : (((p2 → ((p2 → p4) ∧ (((((False ∨ p5) → p5) → p2) ∧ ((False → ((((p5 → p2) ∨ True) → False) → p2)) → (p2 → p1))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962410487495879784999311369800 : ((((True → False) ∧ ((p3 → ((p2 → (False → (p2 ∧ p2))) ∨ (p1 → p5))) ∧ ((p5 → p5) ∧ (True ∧ ((p3 ∨ (p5 → p5)) ∧ True))))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191581379628973108173354241136 : ((p2 ∧ ((p3 → (False ∨ True)) → (p4 ∧ (p3 ∨ p2)))) ∨ ((p4 ∧ (((p4 → p3) ∧ p2) ∧ (((p4 → p1) ∨ p5) ∨ (p5 ∨ p4)))) → p3)) := by
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
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166336178922793376794335626741 : ((p5 ∧ (p2 ∨ ((p3 ∨ p1) → (((p2 → p4) → (p3 ∧ (p2 → (p3 → p2)))) ∧ True)))) ∨ ((((p4 → (p2 → False)) ∧ p3) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185327338751115537454910198221 : ((p3 ∧ (p1 ∧ (False → (((p2 → (p4 → p2)) ∧ p2) → p5)))) ∨ ((p4 ∧ ((False ∨ True) ∧ (((p2 ∧ (p4 → False)) ∧ p1) ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340932613496565276226656894169 : (p2 → ((((p4 ∧ p1) ∨ (p1 → False)) ∧ ((((p4 ∧ (True ∧ ((((p3 → (p4 ∨ p1)) → True) → p3) ∧ p5))) ∧ False) ∧ False) ∧ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3382642097855399737839178522 : ((p1 → False) → (p2 ∨ (((p4 → ((((False ∨ (p3 ∧ (p5 ∨ p1))) ∨ p5) ∧ (p5 → ((True ∨ p2) ∧ False))) → False)) ∨ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h20 := h5 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115048173345244372801436341003 : ((((((p1 ∨ p4) ∨ (p1 ∧ (False → (p3 ∨ p1)))) → p3) → False) ∨ ((True ∧ ((False ∧ ((p1 ∧ p4) ∧ p4)) → p3)) ∨ False)) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45812390700215470789498588443 : (((p1 → (True → (((True ∨ p1) ∧ True) → (((p5 ∧ (((p1 → p1) ∧ (False ∧ p3)) ∧ ((p5 ∨ p5) ∨ p5))) ∨ True) ∨ p4)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135827280055042601785257933582 : ((((p5 ∧ (p4 ∨ (((False ∧ True) → p5) → p4))) → (p5 ∨ p5)) ∧ (p3 ∧ (p1 ∧ (p2 ∨ (p1 ∧ (True → p1)))))) ∨ (False → (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197997523152326383724770136724 : (((True → False) ∧ (((p2 ∨ p2) ∧ p3) → True)) ∨ ((((p4 → (p3 ∨ p4)) ∧ (p2 ∧ ((True → (True ∨ p4)) → False))) ∧ p5) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190222142289382021274934557214 : (((p3 → (((False ∨ (p5 ∨ p5)) ∨ p3) ∧ p5)) ∧ False) ∨ (((p3 ∨ (p2 → True)) ∧ (p4 ∨ ((p3 ∨ (False ∧ p3)) ∧ p4))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248746490504299089044863718353 : ((p3 ∨ p3) ∨ ((False ∨ ((p1 ∨ ((False → p2) ∧ (p3 → ((((p5 ∧ p4) → ((p5 → p2) → (p3 ∨ p1))) ∨ True) ∧ p1)))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54347213675232609089424626846 : (((False ∨ (p4 ∨ (((True ∧ p1) → p2) ∧ True))) ∧ (p2 → ((p5 ∨ p5) ∧ (p4 ∧ (((p2 ∧ p2) → p5) ∧ (p5 ∨ (False → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192689359734374437765495065913 : (((((False → (p5 → p4)) ∨ p4) ∨ (p2 ∨ p4)) → p2) → ((True ∧ (p5 ∨ (p2 ∧ p2))) ∨ (p5 ∨ ((p5 → ((p1 → p3) ∨ True)) ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187145440902837208598951076106 : (((True → p1) ∨ (p2 ∧ (p3 ∨ (p5 → (True → (False → True)))))) → ((False → True) ∧ (((True ∧ p1) ∧ p5) → ((p4 ∧ True) ∨ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51842217026975914816647676428 : (((((p5 ∨ (p1 → ((p4 ∧ ((True → False) ∧ p3)) ∧ False))) ∧ (p2 → p5)) ∧ p2) ∨ (True → (((p4 ∧ (True ∨ True)) → p3) → True))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192633501456621425885787762911 : (((((p4 → ((p1 ∨ p2) ∨ p3)) ∨ p5) ∨ p5) → p5) → (p5 → (True → (((p5 → (p5 → (True → True))) → False) ∨ (False → (p3 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166984655936362845255738753869 : (((p1 ∨ (((p4 ∧ (((p1 ∧ (p2 ∧ p3)) → p3) ∨ (p5 ∨ p2))) ∧ p5) ∨ p5)) ∧ p4) → (True → ((False ∨ p5) ∨ (p3 → (False → p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151651384703333309780650989352 : ((((True → (((p3 → (p2 ∨ p1)) ∧ p5) ∨ ((True → p3) ∨ p4))) ∧ (p2 ∨ p5)) ∧ ((p4 ∨ False) ∨ False)) → ((p3 ∧ (False ∨ p3)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57599679770147059595782623437 : ((((p1 → p5) ∧ p5) → ((((True ∨ ((((p4 → True) → (p1 → True)) ∧ (p3 ∧ (True → p2))) → False)) → True) → (p4 → False)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357401964833031167726870230690 : (p5 → ((True ∨ True) → ((p1 ∨ (p2 ∧ ((p4 ∨ ((p3 → (p5 → p1)) ∧ p1)) → p4))) → (((p3 ∨ p2) ∧ p5) ∨ ((p2 → p4) → p1))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777082659237185696256562075564 : (((p1 ∨ ((p2 → ((p4 ∧ True) → (((False ∨ p2) → ((p3 ∧ (((p1 ∨ p5) → p3) → p1)) → (p1 ∧ False))) ∨ p5))) ∨ (p4 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754925114958951473968684919743 : (((False ∧ (p4 ∨ ((((p4 ∧ ((((False ∧ False) ∨ False) ∨ ((False ∨ p4) → True)) → ((p3 ∧ p5) ∧ (False ∨ p3)))) → p3) → False) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785516448830853823670130996319 : (((p4 ∨ ((p1 ∧ (False ∧ (False ∨ ((((((False ∨ (p2 → False)) ∨ p2) ∧ p5) ∨ (True ∧ (p3 ∧ p1))) ∨ (p1 ∨ p2)) ∧ p5)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330722348151725842871696841566 : (True → (p1 → ((((p3 ∨ (p1 ∧ p3)) ∨ (True → True)) ∧ (False ∨ (p3 → ((p2 ∧ (((p1 → (p5 ∨ p4)) ∨ False) → False)) ∧ True)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225067306661061321242252395975 : (((p1 ∧ p2) ∧ False) ∨ ((((False ∨ (p5 ∨ (p3 ∨ (p1 → (((p5 ∨ False) ∨ p1) ∨ False))))) ∨ p2) ∨ (p2 ∧ (p4 ∧ p2))) ∨ (p2 → p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261279332298142881303285510192 : ((p5 → True) → (((p1 ∧ p5) ∧ ((p2 ∧ (p5 ∨ p1)) → p4)) → (((False ∧ p3) → p5) ∧ (p1 ∧ ((p2 ∨ p4) ∨ ((p3 → p2) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39313513049170991191918330967 : (((p2 ∧ ((((((((p3 ∧ p4) ∨ p1) ∧ ((False → p2) ∧ ((p4 → (p4 → True)) ∨ True))) ∨ False) ∨ False) ∧ p2) ∨ p3) ∧ p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742647001918051528130312054883 : ((((p2 → p4) ∨ (((p2 ∨ p3) ∧ ((True → (((p5 ∧ (p2 ∨ p3)) ∨ ((p1 ∨ p4) ∧ p4)) ∧ p5)) → p5)) ∨ (p3 → (True ∨ p2)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777458540615200966177361573875 : (((p1 ∨ ((True ∨ (False ∧ ((((((p4 ∧ False) → p2) ∨ (False → False)) ∧ p3) ∧ p5) ∧ p5))) → (((p5 ∨ (p1 ∨ p5)) → p3) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122082778344701168730398144231 : (((p4 → ((p1 ∨ (((p5 ∧ p2) → False) ∧ (((((False → p1) ∨ p4) → False) ∨ p5) → ((p3 ∧ p4) ∨ False)))) ∨ p4)) → False) → (p2 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p1 ∨ (((p5 ∧ p2) → False) ∧ (((((False → p1) ∨ p4) → False) ∨ p5) → ((p3 ∧ p4) ∨ False)))) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → ((p1 ∨ (((p5 ∧ p2) → False) ∧ (((((False → p1) ∨ p4) → False) ∨ p5) → ((p3 ∧ p4) ∨ False)))) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214994583518134974920553625232 : (((p5 ∧ p4) → (p3 → False)) ∨ ((((True → p3) → ((True ∨ p5) → p4)) ∨ ((p1 → (p1 → p1)) ∨ False)) ∨ (p4 ∨ ((p4 ∧ p3) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622491294549532795960534265416 : ((((p3 ∧ (False ∨ ((p2 → ((p3 ∨ p4) ∧ p2)) ∧ (p3 ∧ (((p4 → p3) ∨ p4) ∨ (((p1 → p3) ∧ (p5 ∨ p1)) → True)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_200282729143603451519039592783 : (((p2 → (False ∨ p1)) → ((False ∧ p5) ∨ p3)) → (((p1 ∨ (((p2 → (True ∧ False)) ∨ ((p4 → p1) ∧ p3)) → True)) → p5) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205641526418010264177939893662 : (((p4 ∧ p3) ∨ (p4 → (p1 ∧ p4))) ∨ (((((p2 ∧ True) ∨ ((True → ((p3 → p1) ∨ ((p3 ∧ p4) → p1))) ∨ p2)) ∨ p3) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190299710976592526277670366189 : ((((True ∧ (((p3 ∧ p5) ∨ False) → p5)) → p3) ∨ p5) ∨ ((((((p2 → False) → ((p5 ∨ False) → p5)) ∨ (p4 ∨ p5)) ∧ p4) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59638741392907206065981108286 : (((p5 → p3) ∨ (((True → ((((p3 → p4) ∨ p3) → ((p5 → p4) → (p4 ∨ False))) ∧ True)) → (p2 → False)) → ((p1 ∨ False) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40244796763548687805150694514 : ((((p5 ∧ (False ∧ ((p3 → (((((p1 → False) ∨ p5) ∧ (p3 → True)) → ((p2 ∨ (p2 → True)) ∨ True)) → False)) ∨ p4))) ∧ p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198681705339201423175077660983 : ((p4 ∨ ((False → (p4 ∧ False)) → (p2 ∨ p2))) ∨ (((((p4 → False) → False) ∨ p5) ∨ (p1 ∨ (p5 → (((p5 ∨ False) ∨ p3) ∧ p5)))) ∨ p3)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135670778270299336527671484352 : (((p3 ∨ (False → ((p1 ∨ (False ∧ (True → ((p4 → p4) ∧ True)))) → (p3 → p5)))) → ((p3 → (p2 ∨ False)) ∧ True)) ∨ ((p4 ∧ False) → p5)) := by
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
theorem thm_5_vars_48106168903319803684626258446 : ((((True ∧ ((p3 ∨ p1) ∨ p5)) ∨ ((((p5 ∨ p4) ∧ ((p3 ∨ True) ∧ True)) ∧ (p3 ∨ ((True → p3) ∨ p4))) → p3)) → (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186766980541984073355519726121 : (((p3 ∧ (((p1 ∨ p1) ∨ p2) ∧ p4)) → (p1 → (p1 ∨ p1))) → ((p5 → p3) ∨ (((p1 ∨ p2) → (p2 → ((p2 ∨ p2) ∨ p1))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41978693013132563794550232572 : ((((p2 ∨ p3) ∧ (p5 ∨ (((False ∧ p3) → (p2 ∨ (((True ∧ p4) → ((p1 → False) ∧ p1)) ∧ False))) → (False ∨ (True → p4))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323482684218384445941060824915 : (p5 ∨ (((((((p5 ∨ p5) ∨ p3) ∨ p1) ∧ p1) ∨ ((False → p2) → ((p1 ∧ ((p5 ∧ False) → True)) → True))) → False) ∨ ((p5 ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45240705226297175428721305187 : (((p1 ∧ (((((p1 ∧ p2) ∨ ((((True ∧ (True → p2)) ∨ False) → (True → False)) → p4)) → p1) ∨ False) → ((p4 ∨ p4) ∨ p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722248164139674079733985105898 : (((((True ∧ False) ∧ True) ∧ (p2 ∨ ((p5 ∨ p3) → (p5 ∨ (((((p4 ∧ p1) → p1) → ((p1 ∨ (False → p5)) ∧ p5)) → p2) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118132248849443534381436936284 : ((False ∨ (((((p4 ∧ ((p1 ∨ (p4 ∨ (True → (p1 ∨ p5)))) ∧ p5)) → p5) → (p4 ∧ False)) ∧ False) ∨ ((False ∧ p3) ∨ p3))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164752796063478290486080289114 : ((((p1 ∧ ((p2 → (p2 → (p2 ∨ ((p4 → p5) ∨ p1)))) ∧ True)) → (True ∧ p4)) ∨ p5) ∨ (p2 → (((True → p3) ∨ True) → (p4 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41407111293880647197077864235 : ((((((True → (((p3 ∧ ((False ∧ False) ∧ p4)) → True) ∨ p4)) → True) → False) ∨ ((((p2 ∨ p4) → p5) → (p1 ∧ p1)) ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180394781494312050761885400919 : (((p1 ∧ ((((True → (False → p3)) → p2) ∨ p4) → False)) ∨ (p1 → p1)) → ((((p3 → False) ∨ (True ∨ False)) ∨ p5) ∨ ((False → p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
  case inr h5 =>
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
theorem thm_5_vars_347671797204729419485424341018 : (p3 → ((p2 ∨ ((p2 ∧ p1) ∧ p1)) → ((False ∨ True) ∧ (False ∨ (((p2 ∨ ((True ∧ p2) ∧ (p5 ∨ (p2 ∨ True)))) → (p1 ∧ p3)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37460377060623337570645723918 : (((((((((p2 ∧ p3) → p4) → p5) ∧ (True ∧ p1)) ∧ p2) → ((((p5 ∨ (p1 ∨ False)) ∧ p4) ∧ (p1 → p3)) → p3)) ∨ p2) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h25 := h4 h24
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594478314327716606902982592753 : ((((((((((True ∧ p3) ∧ (p4 ∨ p1)) → (p4 → p3)) → False) ∨ (p3 ∨ p1)) → False) ∨ (p2 ∨ (p4 ∨ (False ∧ (p1 → p5))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171658990306202422448244809041 : (((p2 ∧ ((((((p5 ∨ False) → True) ∧ (p5 ∨ p5)) → p3) ∨ True) → p5)) ∨ True) ∨ (((p1 → p5) → p4) → ((p1 → p3) ∧ (False → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938167341714253554732470867288 : ((((p3 → ((p2 → True) → (p2 ∧ p1))) ∧ ((p3 ∧ (False → (p2 ∨ p1))) ∨ ((p3 ∧ (((p4 ∨ p5) ∧ (True ∧ p5)) ∨ p5)) ∨ p3))) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h19.left
          let h22 := h19.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h23 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h23
          -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
          have h25 : (p2 → True) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h24, we can now drive its conclusion.
          let h27 := h24 h25
          -- We need to get the left conjuct of h27 based on <expert-advice>.
          let h28 := h27.left
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h19.left
          let h31 := h19.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h32 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h33 := h2 h32
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h34 : (p2 → True) := by
            -- Implications on the right can always be decomposed.
            intro h35
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h36 := h33 h34
          -- We need to get the left conjuct of h36 based on <expert-advice>.
          let h37 := h36.left
          -- One of the premise coincides with the conclusion.
          exact h37
      case inr h38 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h39
        -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
        have h41 : (p2 → True) := by
          -- Implications on the right can always be decomposed.
          intro h42
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h40, we can now drive its conclusion.
        let h43 := h40 h41
        -- We need to get the left conjuct of h43 based on <expert-advice>.
        let h44 := h43.left
        -- One of the premise coincides with the conclusion.
        exact h44
    case inr h45 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h46 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h45
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h47 := h2 h46
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h48 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h49
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h50 := h47 h48
      -- We need to get the left conjuct of h50 based on <expert-advice>.
      let h51 := h50.left
      -- One of the premise coincides with the conclusion.
      exact h51
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148254954736546261410948401096 : (((True ∧ (((p3 ∨ p4) ∨ ((p4 ∧ False) ∨ True)) ∧ ((True ∨ (True → p3)) ∧ p4))) ∨ (False ∨ (True → True))) ∨ ((p2 ∧ p2) ∨ (p5 ∧ p3))) := by
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
theorem thm_5_vars_263688330940678687488107300372 : (True ∧ ((((True → ((p4 ∧ ((False → p4) → (p2 ∨ False))) → False)) ∨ (p1 → p2)) ∧ (p4 ∧ p1)) ∨ ((p1 ∨ ((False ∨ p5) → p4)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261540912762269893958522221051 : ((p5 → p3) → (p1 ∨ (((p2 ∧ (p1 → p4)) → ((((p5 ∨ p1) → False) ∧ p3) ∧ p5)) ∨ (((p4 ∨ (p4 → (p4 ∧ p4))) → p1) → True)))) := by
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
theorem thm_5_vars_43874716433262769054499717533 : (((((False → p5) ∧ ((p4 ∧ (False → ((p1 → p1) → (p2 ∧ (False ∧ (((p3 ∧ False) ∧ p2) ∨ p5)))))) ∨ p3)) ∧ (p5 → p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136939840929348093252575849533 : (((p4 → p1) ∨ (((((False → False) ∨ True) ∨ p2) ∧ p5) ∨ ((p2 → (p4 ∨ (p1 → (p5 ∧ p3)))) ∨ (False → False)))) ∨ ((p5 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173638832846823782235083955628 : (((p4 → ((False ∨ ((((False ∧ p2) ∨ p3) ∧ False) ∨ (p3 → p3))) ∧ False)) ∧ p4) → (p5 ∨ ((p4 ∧ True) → ((p4 ∨ True) ∧ (p4 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121787567459687836018395824629 : ((((True ∧ (True → p3)) ∨ ((p2 ∨ ((((p2 → p4) ∨ p4) ∨ False) ∧ ((p4 ∧ p5) ∨ p4))) ∨ ((p2 ∧ p4) ∨ True))) → p5) → (p5 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (True → p3)) ∨ ((p2 ∨ ((((p2 → p4) ∨ p4) ∨ False) ∧ ((p4 ∧ p5) ∨ p4))) ∨ ((p2 ∧ p4) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744665477075265875146926949075 : ((((p3 ∧ True) → ((p3 → p1) ∧ (((((p4 → p1) → (p1 → ((p1 ∨ p2) ∧ (p4 ∧ p5)))) ∨ (p3 ∧ (p3 → True))) ∧ p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344671880801537300901305456715 : (p2 → (p2 → ((((((p1 ∨ (p1 → False)) → (p3 → p5)) → p3) ∧ True) ∨ (p4 ∧ False)) ∨ (p2 ∨ (p2 ∧ (((p4 ∨ p3) ∧ p3) ∨ p2)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677474820120531308078381005625 : ((((((((p3 → p1) ∨ (p2 ∨ False)) → False) ∨ ((p1 → ((p1 → True) ∧ p3)) → (p1 → False))) ∨ p5) ∨ (p1 → ((p5 ∨ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200096864313316265060872506611 : ((((p3 ∨ p5) → p1) ∧ ((True → p5) ∨ p5)) → (p5 ∨ (((p1 → p2) → (p1 ∧ ((((p1 ∧ p5) ∧ (p2 ∧ True)) ∧ p5) → True))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937043986488584122368732779323 : (((((False → (p2 → (p3 ∧ p4))) → False) ∧ ((False ∨ ((((True ∨ True) → (False ∧ (p4 ∧ True))) → p5) ∨ p1)) ∧ ((p1 ∧ p4) ∧ p1))) → p5) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (False → (p2 → (p3 ∧ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h13
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : (False → (p2 → (p3 ∧ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h23
        -- False on the left can always be used.
        apply False.elim h23
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h22
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738000919664162734645878839880 : ((((True ∧ p5) ∨ ((((False ∧ p1) ∨ p4) ∨ (False ∨ (True → (((p3 → p3) ∨ (p4 ∧ False)) ∧ (p5 ∧ (p4 ∧ p1)))))) → (p3 ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44925777998858280267205077532 : ((((p1 ∧ p5) ∧ ((p3 ∨ (p4 ∨ (p5 ∨ (p5 ∧ ((((True ∨ True) ∨ p5) → (p5 ∧ p5)) ∨ (p2 ∨ (True ∧ p2))))))) → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319550752341138345276773287757 : (p4 ∨ (((True → (True ∧ False)) → ((False ∧ True) ∧ (p3 ∨ p2))) ∨ ((((p2 ∧ (False ∨ ((True ∧ p2) ∧ p2))) ∧ p1) ∧ p3) ∧ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40322347043617389085474381184 : (((((p4 → ((((False ∧ (p2 ∧ True)) ∨ p3) → (p5 ∨ (p1 ∧ ((p1 ∧ True) → (True ∨ p5))))) ∨ (p2 ∨ False))) ∧ p2) ∨ True) ∨ p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219494489681882586891889775977 : ((p5 ∨ ((p1 ∧ p4) ∨ True)) → ((p2 ∧ (((p3 ∧ (p1 ∧ (p5 → ((p3 ∨ p3) ∨ (p4 ∧ p2))))) → (False ∧ (False ∧ p1))) ∧ p2)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_228874053516737992325355066931 : ((p4 ∨ (False ∧ False)) ∨ ((p5 → ((p3 → p1) → (((((p5 ∧ (p2 ∧ p5)) ∧ (p2 → True)) ∧ (p3 ∧ p1)) ∧ False) ∨ (p5 ∨ p2)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113526080278672159353940586937 : (((((True ∧ p4) ∨ (((True ∧ False) ∨ p3) → p1)) ∨ (((p4 ∧ ((p3 → p2) ∨ p4)) → (p1 ∨ p1)) ∧ False)) ∨ (p4 → True)) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789755370092024000271951569148 : (((p5 ∨ ((p5 ∧ (False ∧ (p1 ∧ p3))) ∨ ((((p2 ∨ (False ∨ p5)) ∧ p4) → (p2 ∧ ((True → p5) ∧ ((p1 → p3) ∧ p3)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317620567168660954576904891449 : (p4 ∨ (((((((False ∧ p1) ∨ p2) ∨ ((True ∧ p2) ∨ (((p3 → False) → p3) → ((True ∧ p5) ∨ (p3 ∨ True))))) ∨ p1) → p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88156640475904587235226718327 : ((((p3 ∨ p5) ∨ (True ∧ p5)) ∧ ((p3 ∨ (p5 → (p4 ∧ False))) ∧ ((p4 ∧ ((p5 ∨ p4) ∨ p5)) ∧ (((False ∧ p5) → p5) → p1)))) → p4) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h7.left
        let h19 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h3.left
      let h28 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h30.left
        let h33 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h37 =>
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h28.left
        let h40 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h41 := h39.left
        let h42 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- One of the premise coincides with the conclusion.
            exact h41
          case inr h45 =>
            -- One of the premise coincides with the conclusion.
            exact h45
        case inr h46 =>
          -- One of the premise coincides with the conclusion.
          exact h41
  case inr h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h50 := h3.left
    let h51 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h51.left
      let h54 := h51.right
      -- Conjunctions on the left can always be decomposed.
      let h55 := h53.left
      let h56 := h53.right
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h59 =>
          -- One of the premise coincides with the conclusion.
          exact h59
      case inr h60 =>
        -- One of the premise coincides with the conclusion.
        exact h55
    case inr h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h51.left
      let h63 := h51.right
      -- Conjunctions on the left can always be decomposed.
      let h64 := h62.left
      let h65 := h62.right
      -- Disjunctions on the left can always be decomposed.
      cases h65
      case inl h66 =>
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h67 =>
          -- One of the premise coincides with the conclusion.
          exact h64
        case inr h68 =>
          -- One of the premise coincides with the conclusion.
          exact h68
      case inr h69 =>
        -- One of the premise coincides with the conclusion.
        exact h64



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_573221050373328593398060781323 : (((p1 → (p1 → (True → ((((p5 ∨ ((p4 ∧ p3) ∨ False)) ∨ (p2 → p2)) → p5) ∨ ((p2 ∨ p1) → (p5 ∨ ((p5 ∨ p4) ∨ True))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



