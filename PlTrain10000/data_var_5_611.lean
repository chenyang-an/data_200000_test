variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641240224640084543489478909670 : (((((p4 ∨ p5) ∨ (((((p1 ∨ (False ∨ (p5 ∨ p5))) → p1) ∧ ((((p2 ∨ (False → p1)) → False) ∨ p4) ∨ True)) → p2) ∧ True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37262469407099476496862667545 : ((((p3 ∧ (p1 → (p2 ∨ ((p3 ∨ ((False ∨ p1) ∨ (False → (True → p1)))) ∨ (p2 ∧ (p3 → ((p3 ∧ p5) ∧ p5))))))) ∧ p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87438643420019331145684865533 : (((True → (((p1 → True) ∨ p4) → p2)) ∧ (p3 → (p4 ∨ (False ∨ (p4 → (((p4 ∧ p4) → (((False → p2) → p1) → False)) ∨ True)))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 → True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865722001512607352373522633931 : (((((p2 ∨ (p4 ∧ (p5 → p4))) ∨ (((((p2 ∧ p5) ∧ p4) ∧ True) ∧ (True ∧ (p1 ∧ p4))) ∨ (p2 ∨ ((p5 ∧ p2) → p5)))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p4 ∧ (p5 → p4))) ∨ (((((p2 ∧ p5) ∧ p4) ∧ True) ∧ (True ∧ (p1 ∧ p4))) ∨ (p2 ∨ ((p5 ∧ p2) → p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341063001219343589119615605623 : (p2 → ((p3 ∨ (p5 → (((((p2 → p5) ∨ (p1 → p5)) ∧ (p4 → p4)) ∨ p2) → ((p4 ∨ (((p2 ∨ True) ∧ p5) → p3)) → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802447252868569348223430016637 : (((p2 → (p1 ∨ (False ∨ (((((p2 ∨ (p1 ∨ (True ∧ ((p3 ∨ (p4 → p3)) ∨ True)))) ∧ True) ∨ p3) → (False ∨ (p5 ∨ p4))) ∨ True)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_733337690796333545646338111126 : ((((p3 ∧ p5) ∧ (p3 ∨ (False ∨ (p3 ∧ (((p2 → ((((p5 ∨ False) ∨ p2) ∧ (False → p5)) ∧ (p2 ∧ p4))) ∧ p4) ∧ (p2 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232700590056272156666908566656 : ((p1 ∧ (p1 ∨ p3)) → ((p4 → False) ∨ ((p5 ∨ True) ∧ (p2 → (((p2 ∧ (p5 ∧ p4)) ∧ (p3 → p5)) ∨ (((True ∧ p1) ∨ p4) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134441215182398009661892125776 : ((((((p5 ∨ ((p4 ∧ (p2 ∨ ((p4 → p3) ∨ ((True ∧ p5) ∨ True)))) → p1)) ∧ (True ∨ True)) ∨ p5) ∧ p1) → p3) ∨ (p5 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709739199026242328418620157621 : ((((False → ((p4 → (p2 → (p3 ∧ p2))) → p4)) → (((p4 → (p2 ∧ ((False ∨ (False ∨ True)) ∨ (p2 ∨ False)))) ∧ p2) → (p1 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62664752311887054177453059609 : ((p4 ∧ ((((p3 ∨ (p3 → (p3 ∨ (False → (p2 → p3))))) ∧ p4) → ((p2 → (p2 ∨ p4)) → (((p4 → p3) ∨ True) ∧ False))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191501242096622774429684944586 : ((False ∧ ((p1 ∧ (p2 ∨ (p5 ∨ (p4 ∨ False)))) ∧ p5)) ∨ ((p2 ∧ p4) → ((p1 ∨ ((True ∨ (p4 ∨ p3)) ∨ p3)) → ((p2 ∧ False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113470381494097378220342917751 : ((((p5 ∨ (p3 ∨ ((((p2 ∨ p2) → (((True ∧ p1) ∧ ((p2 ∨ p3) ∨ p2)) ∧ True)) ∧ p4) ∧ p3))) → p1) ∨ (p5 → False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116895154558295852094345116472 : (((p4 → p2) ∨ (((((((True ∨ p3) ∧ (p1 → p1)) → True) ∧ p4) ∧ p1) ∨ (False ∧ (p3 → p1))) ∨ (p5 ∧ (False → p2)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209074060945851822595913164218 : ((p1 ∨ (p4 ∨ ((p2 ∨ p2) ∧ p5))) → (p3 ∨ (((p2 ∨ p1) ∧ (p2 → p5)) ∨ (((True ∧ (p4 → p4)) ∨ p3) ∨ ((p5 → p4) ∧ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134101692833190301541484964249 : ((((p2 → ((p5 → p4) ∧ (p3 ∧ (p2 → ((p3 ∧ (((p4 ∨ p3) ∧ (False ∧ p3)) ∧ False)) ∨ p1))))) → p2) ∨ False) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323813744902692330385904147562 : (p5 ∨ ((p5 → ((p1 ∧ ((((p4 ∨ True) ∧ p2) → False) → (True ∧ (True ∧ (p4 ∨ p3))))) → p4)) ∨ (True ∧ (p1 → (p2 ∨ (True ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156644913142254370754149033196 : ((((((p1 → ((p2 ∧ ((p1 ∧ True) ∨ (p1 ∨ (p3 → p4)))) ∧ p4)) ∨ False) ∨ p4) → p1) ∧ True) ∨ ((p3 ∨ (p1 ∨ (p2 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184933521350873301343166453392 : (((True → (False ∨ p3)) ∨ (((p5 → False) ∨ (p3 ∨ True)) ∧ p5)) ∨ (p2 → (p1 → (p1 → ((((p4 ∧ False) ∧ (p1 → p1)) → p2) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262207490302400464185496083259 : (True ∧ (((True ∨ ((((((p5 ∧ p5) → p3) → (p2 ∧ (((False → p3) ∨ p5) ∧ (True ∧ p3)))) → p4) ∨ (p4 → p5)) ∧ p1)) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48176897487832013759683642084 : ((((p5 → True) ∧ (((p2 ∨ (p3 → p1)) ∨ (p4 ∧ ((p4 ∧ (p1 ∧ p1)) ∨ (p2 ∨ ((p4 ∧ False) → p3))))) ∧ p3)) → (False ∨ True)) ∨ False) := by
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
    cases h6
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328687820285689312919406292879 : (True → ((p5 ∨ (((((True ∨ True) ∨ p4) ∧ p1) ∨ (p2 ∨ False)) ∨ True)) ∧ (False ∨ (((p5 → p2) ∧ (p5 ∨ p4)) → (True ∨ (False ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48046883998222971502856674900 : (((((p1 ∧ True) ∨ (((p4 ∨ (True ∨ p2)) → True) ∨ p4)) → (((p5 ∨ p4) ∧ (p5 ∨ p2)) ∨ ((False ∨ p4) ∧ p3))) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781633184422858406449040831006 : (((p2 ∨ (p2 ∨ (((p4 ∧ ((p4 ∨ p5) ∨ p4)) ∨ ((p3 ∨ (p3 ∨ ((p1 ∧ True) ∧ ((p1 → p3) → (p5 ∨ p2))))) ∨ False)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65293126525696333427012833043 : ((p3 ∨ (((p1 → p3) → ((p2 ∨ (p1 ∧ p2)) ∧ (((p1 ∨ p1) ∨ (True ∧ (p4 ∧ p3))) ∨ ((p4 ∧ p5) → p2)))) ∨ (p4 ∨ True))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314245727918908968601949204416 : (p3 ∨ (((False ∨ ((False ∨ (p1 ∧ ((p5 ∨ (p4 ∨ (p2 ∧ p3))) → (p1 ∨ p4)))) ∧ True)) ∧ (False → (False ∨ False))) ∨ ((p2 → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196686042039542770843112910379 : ((((((False ∨ p2) → p4) → p4) ∨ p3) ∧ p2) ∨ (((p5 ∧ p3) → p2) ∨ ((True → (p2 ∨ p4)) ∨ (((False ∧ p1) → False) ∨ (p3 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68085342542725800573297965366 : ((p2 → (p4 ∨ ((p2 → False) → ((p5 ∧ ((p4 ∧ (False ∨ p1)) → (True → ((p1 ∧ ((p1 ∧ p2) → p4)) → (p4 → False))))) ∨ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617449574162584153123098439880 : (((((((False ∨ p1) ∨ (p5 ∧ True)) ∧ p2) ∧ (p2 ∧ (p4 → (p4 → ((p4 → False) ∨ (True ∨ ((False ∨ (True → p4)) ∧ p2))))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60794464041862351468431029721 : ((True ∧ (False ∧ ((True ∧ (((p2 ∧ (p4 ∧ p2)) ∨ False) ∨ (False → (True ∧ (False ∨ (p1 → ((True → p1) ∨ p4))))))) ∨ (p5 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47295339828712417188802456521 : (((((p3 ∨ False) ∨ p5) ∧ ((p5 → ((p2 → p5) ∧ (((p3 → p4) → True) → ((p3 ∧ (p4 ∨ p4)) ∨ p2)))) ∨ p3)) ∨ (p4 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319404306221185786938529535035 : (p4 ∨ (((p4 ∧ p1) ∧ (p2 → (((p4 → p4) → (True → (p3 → p4))) → False))) → ((p4 ∧ True) ∧ ((False ∧ ((p5 → p3) → p2)) ∨ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750940895296823787944014002803 : (((True ∧ ((p5 → (((p2 ∧ p4) → p2) ∧ (p4 ∨ p2))) → (p4 → (((p1 → (p3 ∧ (((p3 → True) ∨ p5) → True))) ∨ p2) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231483400219824646242094126211 : (((p3 → p2) ∨ False) → (((((p4 ∧ p3) ∧ p1) → True) ∧ ((True ∧ (False ∨ p3)) ∨ (p3 ∨ p4))) → (((False → p3) → p3) ∨ (True → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698019006775969520632682768608 : (((((((p2 ∨ (p4 → p3)) ∨ (p5 ∨ (p3 ∨ p1))) → p5) ∨ p5) ∨ (False → ((True ∧ (p4 → (((p5 → p3) ∧ False) → True))) ∧ True))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129282053610039878657444764720 : ((((((True → p5) → p5) ∨ True) → ((True ∧ (((p4 ∧ p5) ∧ p3) ∧ (p3 ∧ (p5 ∧ p3)))) ∧ (True → False))) ∨ True) ∧ (True ∨ (p1 ∧ p3))) := by
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
theorem thm_5_vars_48292789342364763901810924189 : (((p5 ∧ ((((p4 ∨ False) ∧ (p3 ∧ (p2 → (p1 ∧ (p3 ∧ p3))))) ∨ p3) → ((p1 ∧ p5) ∧ ((p3 → p1) ∧ p2)))) → (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135379346615912893362527067157 : ((((p3 ∨ (False ∧ (((((True ∧ False) → (p1 → p1)) → p5) ∧ True) ∧ (p2 ∨ True)))) ∨ True) ∨ (p4 ∧ (p2 → False))) ∨ (p2 ∨ (p5 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38051292310953935409670251894 : ((((((p3 → (((p5 → p4) ∧ (p3 → p4)) → ((((p5 → True) ∨ p4) → p3) → p5))) → False) ∨ (False → p1)) → (p4 ∨ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650277710277098216108539334423 : (((((((True → p3) → False) ∧ (((p5 ∨ p3) ∧ ((p2 → (p5 ∧ p1)) ∧ p4)) ∨ False)) → (((p4 ∨ p4) → p1) ∨ True)) ∧ (False → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149843567538354971669082451140 : ((p1 ∨ ((p5 ∨ p4) ∨ ((p4 → p1) ∨ ((((p5 → p4) → p3) ∧ True) → ((p4 ∨ (p3 ∧ True)) ∨ True))))) ∨ ((p2 ∨ p3) → (p4 ∧ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259384352408427713341236220178 : ((False → p3) → (((False → ((True ∨ ((((p3 ∨ True) → True) → p3) → ((((False → True) ∧ p4) ∧ p3) ∨ p3))) → False)) → p4) → (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((True ∨ ((((p3 ∨ True) → True) → p3) → ((((False → True) ∧ p4) ∧ p3) ∨ p3))) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (False → ((True ∨ ((((p3 ∨ True) → True) → p3) → ((((False → True) ∧ p4) ∧ p3) ∨ p3))) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h9
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357104564965942672117347807686 : (p5 → ((True ∨ (True ∨ p2)) → (True → ((p4 ∧ (False → p4)) ∨ (((p4 ∨ (((p5 ∧ p2) ∧ p4) → p3)) → p3) → ((p4 ∨ True) ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170062166360961441072055137812 : ((((((p3 ∨ p1) → (p4 ∧ p4)) → False) → (p5 ∨ p2)) → (p4 ∨ (p5 → p5))) ∧ (((p1 ∧ True) → False) → ((p1 ∧ False) → (p1 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147155032445499182608779831397 : (((p3 ∧ ((p5 ∨ (p2 → p3)) → ((((p3 ∧ p5) ∧ True) → (p1 → p4)) ∨ (p3 ∧ (p1 ∨ p5))))) ∧ False) ∨ ((p1 ∧ p3) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135903079323712528581467772525 : ((((False ∨ (True ∨ ((p2 ∧ p3) ∧ ((p2 ∨ p3) → p4)))) → p3) → ((((p3 ∧ p5) ∨ p3) ∨ (False → p1)) ∧ p3)) ∨ ((False ∨ p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ (True ∨ ((p2 ∧ p3) ∧ ((p2 ∨ p3) → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313052140136225434102414503999 : (p3 ∨ (((((True ∧ (p1 ∨ p2)) → True) → (True → ((p5 ∧ (((p2 → (p5 ∧ ((p5 ∧ p3) ∨ p4))) ∨ False) ∧ True)) ∧ False))) → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p1 ∨ p2)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228539808714460960944441041555 : ((p1 ∨ (p3 ∧ p4)) ∨ ((((((p4 → (False ∧ p5)) → p4) → False) → (((p3 ∨ ((False ∨ (False ∧ True)) → p2)) → p2) ∨ p2)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48961540232290478176365309601 : (((((((p3 → p3) ∨ (((p4 ∨ p1) ∨ p5) → True)) → ((p2 ∧ (False ∨ (p2 → False))) ∨ p3)) ∧ False) ∨ p2) ∨ ((p4 ∨ p2) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221193870271271840036897159778 : (((p1 ∨ True) ∨ p1) ∧ ((((p4 → ((False ∧ True) → ((p3 ∧ True) ∧ p4))) → ((p2 ∨ p1) ∨ False)) ∨ p1) → (p2 ∨ (p5 ∨ (True ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_657098216214660138847271845040 : ((((((p2 ∧ p3) ∧ True) ∨ (((((p5 → p1) ∧ (p1 ∧ p5)) ∧ (p3 ∧ p4)) ∧ (False → True)) ∨ ((False ∨ True) ∧ False))) ∨ (p2 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646899899325464051338114091398 : ((((p2 → (True ∨ (((p2 → False) → (p1 ∨ True)) → (p4 ∧ (((p3 → p4) ∨ False) → (((True ∨ p4) ∨ False) ∨ (False ∨ p2))))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192484015699441162315073444838 : ((((True → (p2 ∨ False)) ∧ (p4 → (True ∧ p4))) ∨ p3) → (((((False ∨ ((True ∨ p2) → (True ∧ p1))) ∨ p5) → False) ∧ p5) → (p5 ∧ p1))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h14 : ((False ∨ ((True ∨ p2) → (True ∧ p1))) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h17 : ((False ∨ ((True ∨ p2) → (True ∧ p1))) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311176824266781949241498975487 : (p2 ∨ ((False ∨ True) → (((False ∨ ((((p4 ∧ True) → True) → p3) ∨ ((p2 ∨ True) ∨ (((p4 ∨ True) ∧ p1) → p3)))) ∨ (p1 → False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167397621317118015396017975566 : ((((p1 ∧ p4) ∨ ((p5 ∧ p4) ∨ (True ∨ ((True → False) ∧ (p3 ∧ (False ∨ p4)))))) → p3) → (((p3 ∨ p1) ∨ (True ∧ p2)) ∨ (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p4) ∨ ((p5 ∧ p4) ∨ (True ∨ ((True → False) ∧ (p3 ∧ (False ∨ p4)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338865741692719284784510589526 : (p1 → ((p5 → False) ∨ ((p1 ∧ p3) ∨ ((True ∧ (True → (((((True ∧ False) ∨ p4) ∨ p4) ∨ ((p5 ∨ p4) → (True ∧ p3))) → p3))) ∨ True)))) := by
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
theorem thm_5_vars_692752807423264748938509726148 : ((((((True ∧ (p2 ∨ p5)) ∨ False) ∨ (p2 → (((True ∨ p3) ∧ p5) ∧ p1))) ∧ ((True → p3) → ((p2 ∧ ((False ∨ False) → p2)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305604702738121869681037931023 : (p1 ∨ ((p4 → (p1 ∨ (p5 ∧ (((p3 → False) ∨ (False ∧ p4)) ∨ p3)))) ∨ (((True ∨ p4) → ((p5 ∨ (False ∨ p1)) → (True → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119568391596681851258497989612 : ((p5 → ((((p4 → p3) → (True ∨ p1)) ∧ p4) ∧ (((True → p1) → ((p4 ∧ ((p3 ∨ True) ∧ p2)) ∧ (p1 ∨ False))) ∧ p5))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352046980475648579452598664012 : (p4 → ((p2 ∨ ((p5 → True) → ((p1 → p3) → p3))) → (p4 ∧ ((p1 ∧ p1) ∨ (False ∨ ((((p5 ∨ (False ∧ p3)) ∧ p3) → p1) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64343553722933667275414457934 : ((p1 ∨ ((p2 → ((p3 ∨ (p2 ∨ p3)) → ((True ∨ p4) → (p5 ∧ (p4 ∨ ((p5 ∧ (p1 ∧ p3)) ∨ ((p4 ∨ p1) → p3))))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58844208418527451891222965154 : (((True ∧ p2) ∨ ((((((((p4 ∨ p4) ∨ (p2 ∨ p3)) ∨ p5) ∧ False) ∧ True) ∧ ((False ∨ (p3 → p1)) ∨ (p5 ∨ p1))) ∧ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42078703556255213485901527457 : ((((p1 → p5) ∨ ((((p1 ∨ p3) ∨ ((p2 ∧ p2) ∨ (p5 ∧ p1))) → (p1 ∧ p3)) ∨ ((False → (True ∧ False)) ∧ (p3 ∧ p4)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141244010474278319293144745288 : ((((p4 ∧ p4) → (True → (True ∨ True))) → ((((p5 → (((True ∧ p2) ∨ False) ∧ p2)) ∨ p5) ∨ (True → False)) ∧ False)) → (True ∧ (p4 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p4) → (True → (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∧ p4) → (True → (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h9
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318587309630276609843127665298 : (p4 ∨ (((p2 ∨ (((True → (False ∧ ((p5 ∧ (p5 → True)) → (True ∨ False)))) ∧ p4) ∧ (False ∨ True))) ∨ ((True ∧ p4) → p4)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782473006713539082767032006709 : (((p3 ∨ (((True → ((((p3 → (p4 ∧ True)) → True) ∧ p4) ∧ False)) → (((False ∨ p3) ∧ p5) ∧ ((p1 ∧ p3) → (p4 ∧ False)))) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h8.left
  let h16 := h8.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197150715652105111417596164816 : (((p2 → ((False ∧ (p3 ∨ p1)) ∧ True)) ∨ p2) ∨ ((((p4 ∨ p2) ∨ p4) → p5) → ((((False ∧ p4) ∨ False) ∨ ((p3 ∧ p5) ∨ p5)) → p5))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137512500399774969375152723274 : ((p5 ∧ ((((p3 ∧ p1) ∨ (p2 ∧ False)) ∧ p3) ∧ ((False ∧ p5) → (p3 → ((p3 ∧ (p3 → (p1 ∧ p5))) ∧ p5))))) ∨ (True ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83323824564980591120857917667 : ((((False → ((p3 ∧ p5) ∨ (True → False))) → ((p1 ∨ (((p1 → p4) ∨ True) → p4)) ∧ False)) ∧ (p5 ∨ (False ∨ ((p1 ∨ p1) ∧ p2)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False → ((p3 ∧ p5) ∨ (True → False))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (False → ((p3 ∧ p5) ∨ (True → False))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h15
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : (False → ((p3 ∧ p5) ∨ (True → False))) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h20
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264833371702803841642754866062 : (True ∧ ((False ∨ p5) ∨ ((p1 → (p1 → (((p5 ∧ p1) ∧ p1) ∧ ((p4 ∧ p3) ∨ p2)))) ∨ ((False ∧ (p2 ∧ p2)) → ((p5 → p1) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_307434723034088588704785490744 : (p1 ∨ (p5 ∨ (((((((p5 → p4) → (p1 ∧ (((((True → p1) ∨ p1) ∨ p5) → p4) ∨ p1))) ∧ p5) ∨ p5) ∨ p4) ∧ True) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_169005798434529723779799558967 : ((p1 → (((p4 ∧ False) → (p5 → False)) → (((((p1 ∨ True) ∧ True) → p3) ∨ True) → p5))) → ((p3 ∧ ((True → False) → p3)) → (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621905900828474594684592599590 : ((((p1 ∧ ((p4 ∨ p4) → ((((True → ((p2 ∨ (p4 → (p3 ∧ (((p5 → False) ∧ p1) → False)))) → p2)) ∧ True) ∧ p4) → p3))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158271143941575302194845689678 : (((p2 ∨ (p1 → p2)) ∨ ((p4 ∧ (((True ∨ (p1 ∧ (p2 ∧ (p3 ∧ p4)))) ∨ False) ∨ False)) ∨ False)) ∨ (p3 ∨ (p2 → (True ∨ (p1 ∨ p3))))) := by
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
theorem thm_5_vars_185095786585964699087506050834 : (((p5 ∨ p4) ∨ ((p4 ∧ p4) ∧ (((True → p2) ∨ p5) ∧ p2))) ∨ (p2 ∨ (False → ((((False → p3) ∨ p5) ∧ p2) ∧ (True ∨ (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588260101212976585864637803469 : ((((((p4 ∧ ((p3 ∧ (p4 ∨ p3)) ∨ p2)) ∧ ((((p2 ∨ p2) ∧ False) ∧ p4) ∧ (p5 ∨ (p1 ∨ ((p3 ∨ p1) ∨ p4))))) ∨ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341093113190177580854577289334 : (p2 → ((p2 → ((((p3 → True) ∨ False) ∧ (True ∨ (((p3 → p1) → False) ∨ ((p4 ∧ True) ∨ (p1 ∨ (p5 → p5)))))) → (False ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184701446154251812137893008839 : ((((False ∧ ((False → True) ∨ p2)) → p3) → (p4 ∧ (p4 → p1))) ∨ ((p3 ∧ ((p2 ∧ (False ∧ ((False ∧ p5) ∨ p3))) ∨ (p5 ∨ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189762487318494675793879461007 : ((p5 ∨ ((p3 ∨ (p2 ∧ False)) ∨ ((p4 ∧ True) ∨ True))) ∧ ((p5 → p1) → ((False ∧ ((p4 ∨ ((p3 ∨ (True ∨ False)) ∨ p5)) ∨ False)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197938097455524593653704934980 : (((True ∧ p4) ∧ (p2 ∨ ((False ∧ p3) ∧ p4))) ∨ ((((p2 ∧ (True → (False ∧ (True → p2)))) → (p5 ∧ (False ∧ (p3 ∧ p3)))) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (True → (False ∧ (True → p2)))) → (p5 ∧ (False ∧ (p3 ∧ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h3.left
    let h20 := h3.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59091782013778745085511704022 : (((p5 ∧ p4) ∨ (((((p4 ∧ p3) ∧ (((p1 ∨ (p2 → (p5 → ((True → p3) ∨ p3)))) ∨ p1) → p5)) ∨ p1) → (p2 ∨ p1)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909678110904980386779046704061 : ((((p3 ∧ (False → (False ∨ ((p2 → (p3 ∨ (p4 ∧ p1))) ∨ ((p4 → (p3 → p2)) → p3))))) ∧ (((p1 → True) ∧ True) → (p4 ∧ p1))) → p1) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 → True) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153797127864710959014212679020 : ((p4 → (p5 → ((True ∧ ((False ∨ (True ∨ (((p3 ∨ (p1 ∨ False)) → p3) ∧ True))) → p3)) ∧ (False ∧ True)))) → (p5 ∨ ((p5 → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614544705195118279712743784626 : (((((((((p2 ∧ False) → p5) ∨ True) ∨ (p1 ∧ p3)) → (p3 ∧ (p2 ∧ ((p2 → p5) ∨ False)))) ∧ (True ∨ (p5 ∧ (p1 ∧ p2)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_135018584027988786451489501211 : (((True → (p4 ∨ ((p4 ∧ p2) ∧ (((p5 ∧ p2) ∨ (False → p1)) ∧ (p5 → (False → (False → p2))))))) ∧ (True ∧ True)) ∨ ((True ∨ p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678771427198674424783799432564 : (((((p3 → False) → (p2 ∧ ((((False ∨ p4) → ((p2 ∨ False) ∧ ((p5 ∨ p1) ∧ p5))) ∧ p5) ∧ p3))) ∨ (((p4 ∧ p4) → p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18753299550884212255002414402 : (((((p5 → (p4 ∨ ((((p4 ∨ True) ∧ ((p3 ∧ p4) ∧ p2)) ∧ False) ∧ p3))) ∨ True) ∨ False) ∨ (((p3 ∨ False) → (p4 ∨ p5)) ∧ p4)) ∧ True) := by
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
theorem thm_5_vars_317105657941644056265077621342 : (p3 ∨ (p5 → ((p1 ∨ ((((False ∨ (p3 → (((p1 → (True → p5)) ∧ True) → p2))) ∧ ((p5 → p4) ∧ p2)) → False) ∨ True)) ∧ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48062956914002871571905790553 : (((((((False → p1) ∧ (p5 ∨ p4)) → p1) ∧ p4) → (((True ∧ p1) ∨ p4) ∧ ((p5 ∨ p4) ∨ (True ∨ (p3 ∨ p3))))) → (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200549213087993572995186482271 : (((p1 → p2) → (((True ∧ p5) ∧ p1) ∨ True)) → (((p5 ∨ p2) → False) ∨ ((True ∧ (False ∧ True)) → ((p2 ∧ p1) ∧ ((p4 → False) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118325511143076472925678579092 : ((p2 ∨ ((((((True ∨ ((((((False ∨ p4) → p1) ∧ p2) → False) ∧ p3) ∨ p1)) → p5) → p3) ∧ (p1 ∧ p2)) ∨ p3) ∧ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721433087579609417843201181090 : ((((p1 ∧ ((False ∨ p4) → False)) → (p5 ∨ (((((False ∧ p4) ∨ p2) ∧ False) ∧ (p1 → ((p3 → p3) → (p1 → (p1 ∧ False))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317808310330845033008422665973 : (p4 ∨ ((((p4 ∧ ((p2 ∧ p5) ∧ p1)) ∧ p2) ∨ ((True → (((p2 ∧ True) → True) ∧ ((False ∧ p1) → ((p4 ∧ p3) ∧ p1)))) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_784554587663432838933629597992 : (((p3 ∨ (False ∨ (p2 ∨ ((((p2 ∧ ((p2 ∨ p3) → (p5 ∧ p1))) → (p4 ∧ False)) ∧ p3) → ((p1 ∧ (p5 ∨ p2)) → (False ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231398328441751455250858936893 : (((p1 → p1) ∨ True) → (((False → (p3 → (True → p3))) → False) → ((p1 ∨ p4) ∧ (((p2 ∧ p2) ∧ p2) ∧ ((True ∧ (p2 → p5)) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h10
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h16
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h22
    -- False on the left can always be used.
    apply False.elim h26
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h27 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h28 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Implications on the right can always be decomposed.
      intro h30
      -- Implications on the right can always be decomposed.
      intro h31
      -- False on the left can always be used.
      apply False.elim h29
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h28
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h34 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h35
      -- Implications on the right can always be decomposed.
      intro h36
      -- Implications on the right can always be decomposed.
      intro h37
      -- False on the left can always be used.
      apply False.elim h35
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h38 := h2 h34
    -- False on the left can always be used.
    apply False.elim h38
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h39 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h40 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h41
      -- Implications on the right can always be decomposed.
      intro h42
      -- Implications on the right can always be decomposed.
      intro h43
      -- False on the left can always be used.
      apply False.elim h41
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h44 := h2 h40
    -- False on the left can always be used.
    apply False.elim h44
  case inr h45 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h46 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h47
      -- Implications on the right can always be decomposed.
      intro h48
      -- Implications on the right can always be decomposed.
      intro h49
      -- False on the left can always be used.
      apply False.elim h47
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h50 := h2 h46
    -- False on the left can always be used.
    apply False.elim h50
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h51
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h52 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h53 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h54
      -- Implications on the right can always be decomposed.
      intro h55
      -- Implications on the right can always be decomposed.
      intro h56
      -- False on the left can always be used.
      apply False.elim h54
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h57 := h2 h53
    -- False on the left can always be used.
    apply False.elim h57
  case inr h58 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h59 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h60
      -- Implications on the right can always be decomposed.
      intro h61
      -- Implications on the right can always be decomposed.
      intro h62
      -- False on the left can always be used.
      apply False.elim h60
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h63 := h2 h59
    -- False on the left can always be used.
    apply False.elim h63
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h64 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h65 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h66
      -- Implications on the right can always be decomposed.
      intro h67
      -- Implications on the right can always be decomposed.
      intro h68
      -- False on the left can always be used.
      apply False.elim h66
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h69 := h2 h65
    -- False on the left can always be used.
    apply False.elim h69
  case inr h70 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h71 : (False → (p3 → (True → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h72
      -- Implications on the right can always be decomposed.
      intro h73
      -- Implications on the right can always be decomposed.
      intro h74
      -- False on the left can always be used.
      apply False.elim h72
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h75 := h2 h71
    -- False on the left can always be used.
    apply False.elim h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115522546284088413329272480972 : ((((p1 ∨ True) ∨ ((p3 ∨ (p4 → p4)) → p4)) → (((p2 ∨ False) ∨ (((False ∧ p2) ∧ p1) ∨ ((True → p5) → p2))) ∧ p3)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151467814494920591265189351389 : (((((p4 → (((p5 ∧ (False ∧ p5)) → ((p2 ∨ (p5 ∧ p4)) ∧ True)) → True)) → p3) → False) ∨ (p3 ∨ p3)) → ((p5 ∧ p4) ∨ (p4 → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54554339293055583253623203055 : (((p2 ∧ (((p1 ∧ (p4 ∧ p3)) → False) → False)) ∨ (p4 → (p3 ∨ (((False → p3) ∧ ((False ∨ False) → ((p4 ∨ p4) ∨ p4))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892812257220825371740524400480 : ((((((p4 ∨ True) ∨ ((p5 → p2) ∨ (p5 ∧ (p1 → (p2 → (((p4 ∨ p3) ∨ p3) ∧ p4)))))) → (p1 ∧ False)) ∧ ((p1 ∧ True) ∨ p3)) → p5) ∧ True) := by
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
    have h7 : ((p4 ∨ True) ∨ ((p5 → p2) ∨ (p5 ∧ (p1 → (p2 → (((p4 ∨ p3) ∨ p3) ∧ p4)))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : ((p4 ∨ True) ∨ ((p5 → p2) ∨ (p5 ∧ (p1 → (p2 → (((p4 ∨ p3) ∨ p3) ∧ p4)))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45739903089231109112177684658 : (((False → ((p4 ∧ (((p4 ∧ ((p2 → p5) → (p4 → (((p5 ∨ p5) ∨ ((True ∨ True) → p2)) ∨ p3)))) → p3) ∨ p5)) ∧ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



