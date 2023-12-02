variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679614536979141990954613898243 : (((((False ∨ ((True → (True ∨ p1)) ∨ (((p2 ∨ (((False → True) ∧ p3) ∧ p1)) → False) ∨ p2))) ∧ True) → (p3 ∨ (p1 → (p3 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136514176122074684826169979558 : (((True ∨ (p1 ∧ False)) ∧ ((((p1 ∨ True) ∧ False) ∨ ((p5 ∧ ((p3 ∧ p1) ∨ p2)) → (True ∧ (True ∧ p5)))) → p5)) ∨ ((True ∧ False) → p2)) := by
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
theorem thm_5_vars_636373567200242403842624403502 : (((((((False → True) → (False ∨ False)) → (p4 ∧ ((p3 → ((p3 ∨ p4) ∨ p5)) ∨ p4))) → (p3 → (False ∧ (False → (p4 ∨ p4))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49690570314432900963996508189 : ((((True ∨ p4) ∨ (p1 ∧ (((False ∨ p3) → p3) ∨ (((p4 ∧ True) ∨ (p1 → p3)) ∨ ((p1 ∨ p5) ∨ p3))))) → ((p4 ∨ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193435660526739450384233687372 : (((False → True) ∧ (((p4 ∧ p1) ∧ p1) ∨ (p4 ∨ p5))) → ((False ∨ ((p5 → p3) → p3)) ∨ ((p5 ∨ (p3 ∧ p1)) ∨ ((False ∨ p3) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158538522694069990654360964177 : (((p1 → p4) → (((p1 ∨ False) ∧ ((p5 ∧ False) → (p1 ∨ p3))) ∨ (((True → p5) ∧ True) ∧ p1))) ∨ ((p1 ∨ p4) → ((True → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669548601071712535948498780875 : (((((p3 → ((p1 → (p5 ∨ (p2 ∧ ((p3 ∨ (((False ∨ p5) ∨ False) ∨ False)) → p5)))) ∨ False)) → (p2 → p3)) ∨ (p3 → (p1 → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65113132980913571707034118840 : ((p2 ∨ (p5 ∨ ((((((False ∨ True) → p3) ∧ (p4 → p2)) → False) ∧ ((p3 ∧ p3) ∧ ((p5 ∨ p4) → (p2 ∧ p4)))) → (p5 ∨ p2)))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (((False ∨ True) → p3) ∧ (p4 → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    -- Implications on the right can always be decomposed.
    intro h12
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : (p5 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h8
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51312347095345390633690569577 : (((p3 ∨ ((True ∧ p3) ∨ ((p3 → ((True ∨ (((p2 ∧ p5) ∨ p4) ∧ p5)) → True)) → p5))) ∨ (((p5 → (p3 → p1)) ∧ False) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118686316706378292862372025175 : ((p5 ∨ (((p4 → p4) → (p2 → ((True ∧ ((p3 ∧ ((p4 ∨ ((p2 ∨ p1) → p5)) ∨ (p3 → p3))) → p3)) → p5))) ∧ True)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148496447598601714759899622733 : ((((p3 → (p3 ∧ p5)) ∨ ((p5 ∨ p3) ∨ ((p1 → p2) ∧ False))) ∨ (((False ∧ p4) → (p2 ∧ True)) → p3)) ∨ (p4 → ((p1 ∨ p4) ∨ p1))) := by
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
theorem thm_5_vars_144751841987651171346349614584 : (((((((p4 ∧ (p5 → p4)) ∨ True) → (p2 ∨ (p1 ∨ p1))) ∨ (True ∨ p2)) ∨ False) ∨ (p1 → (True ∧ p3))) ∧ ((False ∨ p1) ∨ (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37762885743262513351148334039 : ((((((p3 ∨ p5) → p1) ∧ (((p3 ∨ (False → ((p1 ∨ ((p1 ∧ (p3 ∨ p2)) ∧ (True ∧ True))) ∧ p1))) ∧ p3) → p3)) → p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245147505999759191338415169440 : ((p2 ∧ True) ∨ (p5 ∨ (p3 → (((p5 → p2) → p1) → (p5 → (((((((p4 ∧ p1) ∧ p3) ∨ p5) → p2) ∨ (p1 ∧ p3)) ∨ p5) ∨ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158984607492460817671630904157 : ((p3 ∨ ((((p4 ∨ p4) ∨ False) ∧ (p3 → p5)) → ((p3 ∧ (((p4 ∧ p4) → True) → p1)) ∨ True))) ∨ (((False ∨ p3) ∨ (p1 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140593118856866733396223657220 : ((((p4 ∨ (((p4 → p3) ∨ p3) ∨ ((p3 ∧ (p3 ∧ (p2 ∨ p3))) ∧ False))) ∨ p1) → ((True ∨ p3) ∨ (p1 ∧ p4))) → (p3 ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356671749702799280184407135742 : (p5 → ((p5 ∨ (p5 → (((True ∧ p2) ∧ p3) ∧ p5))) → ((p2 → ((False ∧ (False → True)) ∨ ((p2 → False) ∨ (p2 ∧ (p5 ∨ p4))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325638439179912379949262163698 : (p5 ∨ (False ∨ (((p5 ∧ ((True → p5) ∧ p2)) ∨ p3) ∨ ((p1 ∨ ((p4 ∧ True) ∨ (p4 ∧ True))) → ((False → (p3 → False)) ∨ (p4 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607146272935973817473941322431 : ((((((p2 ∨ (((False ∨ p4) → (p1 ∨ p3)) ∧ True)) → (((p1 ∧ (p4 ∨ (p5 → (p1 → p1)))) ∧ (True → False)) → p5)) ∧ p1) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123468874535834689470256890708 : (((p5 → ((((False ∨ True) → (((p3 → p1) ∨ p5) ∧ ((p3 → True) → False))) ∧ p5) ∨ p1)) → ((p2 ∧ p2) ∧ (p3 ∧ False))) → (p1 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → ((((False ∨ True) → (((p3 → p1) ∨ p5) ∧ ((p3 → True) → False))) ∧ p5) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356744465073966734821397849441 : (p5 → ((p4 ∨ ((p4 ∨ (p4 ∨ True)) ∧ p3)) ∨ (p3 ∨ (((((p4 → False) ∨ (p3 ∧ False)) → (False ∨ p4)) ∨ p3) → (p5 ∨ (p2 ∨ p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51932796563328431600828535109 : (((((p1 → p4) → (((p2 → p3) ∨ p3) ∨ (p3 → p1))) → (p1 ∨ (p3 → False))) ∨ ((p3 → (True ∨ (p2 → (p3 ∧ p5)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776137674433433024577364029705 : (((p1 ∨ ((((p4 ∧ ((True → p5) ∨ (p1 ∧ (True ∨ (((True ∧ (True ∧ (p3 → (p3 → p5)))) ∨ True) ∧ p4))))) → p1) ∨ p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622878401904946362896898112425 : ((((p5 ∧ ((((p5 → p3) → (p4 ∧ p4)) ∧ ((((p1 ∨ (True → (p2 ∧ False))) ∨ (p3 ∨ p2)) ∨ p3) → (p4 ∨ True))) → p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38221436942226009631741705214 : (((((p4 ∧ p2) → ((((p5 ∧ p2) ∨ (False ∧ p4)) ∨ (p4 ∧ ((p2 → True) → (p5 → False)))) ∨ p5)) → (p1 ∧ (p1 → p5))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312713388266348724787824336624 : (p3 ∨ ((((((((p4 ∨ p1) ∨ False) ∨ True) ∨ (p3 ∧ p4)) ∧ p5) ∨ (p4 → (p2 ∨ True))) ∨ ((p3 → p2) ∧ (False ∨ (p3 ∨ p5)))) ∧ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674717810236142435768749805061 : ((((p2 → (p2 ∨ (((((p1 → ((p1 ∨ (p5 → p1)) ∨ p2)) ∨ (False ∧ p2)) ∧ (p1 ∨ p4)) ∨ p4) ∧ p4))) → (True → (p2 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47292448540253389037073928355 : (((((p2 ∧ True) ∧ False) ∧ (((p5 ∧ (p2 ∧ (True → ((False ∨ (p2 ∧ p4)) → p1)))) → p2) → (p1 ∧ (p4 ∨ p2)))) ∨ (p5 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191358848750882547511125186944 : (((p4 ∨ False) ∨ (((False → p5) ∧ p3) → (p4 ∧ p3))) ∨ (((((((p3 → (True ∨ False)) → True) ∧ p4) → True) ∨ (p1 ∧ p5)) ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133669690185444701616890998147 : ((((((p1 ∨ (((False ∨ ((p5 ∨ p4) → (p4 ∧ p1))) ∨ p2) → p5)) ∧ p1) ∨ (False ∨ True)) → (p3 ∨ False)) ∧ True) ∨ (True ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115085614611051060974181910050 : (((p1 ∨ ((((p2 ∨ (p3 ∧ p2)) ∨ (p5 → True)) → p2) → p2)) ∨ ((p3 ∨ p4) ∨ ((False ∧ (p3 → (p4 ∨ False))) ∨ p4))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p3 ∧ p2)) ∨ (p5 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340761022632149866071861031478 : (p2 → (((p1 ∨ ((((p4 ∨ False) ∨ (((False ∨ (p1 → p4)) → (((True → p2) ∧ p4) ∧ p3)) → (p1 ∧ p2))) ∨ p3) ∨ p2)) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308589925670385912253307381854 : (p2 ∨ ((((p2 ∧ p3) ∨ p1) ∨ ((((((p4 ∨ p4) → True) ∧ p2) ∨ p2) ∨ (False ∧ p4)) ∨ ((((False → p4) ∨ False) ∨ True) ∨ p3))) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63020060598543935405194507650 : ((p4 ∧ (p4 → (((p3 → ((False ∧ (((p3 ∧ p3) ∧ False) ∧ ((p3 ∨ ((True ∧ p2) → True)) → (True ∨ p3)))) → p5)) → p3) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149701175857301654970280506484 : ((p5 ∧ ((False → (p1 → p1)) → (((((p5 → p5) → True) → (True → p2)) → (True ∧ p2)) ∧ (p2 ∨ p5)))) ∨ (((p4 ∨ p4) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197995760327798068698202125316 : (((p5 ∨ p4) ∧ ((p3 ∨ p5) ∨ (p3 ∨ p2))) ∨ ((False ∨ ((p1 ∨ True) ∨ p3)) ∨ (p1 ∧ ((p5 → p4) → ((True ∧ (True ∨ True)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175045352390276393378287403869 : ((p2 ∧ ((p3 ∨ (True ∧ ((((p1 ∨ p2) ∨ p2) → (False ∨ True)) ∨ True))) → False)) → ((p3 ∨ (p5 ∨ (((True ∨ p4) → True) → p1))) → False)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ (True ∧ ((((p1 ∨ p2) ∨ p2) → (False ∨ True)) ∨ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∨ (True ∧ ((((p1 ∨ p2) ∨ p2) → (False ∨ True)) ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p3 ∨ (True ∧ ((((p1 ∨ p2) ∨ p2) → (False ∨ True)) ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137188427021015802590526660992 : ((False ∧ (((False ∧ p5) → p2) → ((p4 ∧ (True → (((p1 ∧ False) → p1) → ((p3 ∧ p4) → (p3 ∨ p5))))) ∨ False))) ∨ ((p3 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340698964646588213663172369544 : (p2 → ((((False ∨ (p1 → ((True ∧ False) ∧ (((((p3 → p4) ∧ p2) ∧ (((p5 ∨ p1) ∧ p4) → True)) ∨ False) ∨ p4)))) → p4) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135011168920009175592484946999 : (((p2 ∨ (True ∧ (((p1 ∨ True) → p4) ∧ (p4 ∧ ((((p5 ∨ p1) ∧ p2) ∨ p3) ∧ (p2 ∧ p1)))))) ∧ (False → True)) ∨ ((True → False) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167913344257086852890152857373 : (((p3 ∨ ((((p5 ∨ p3) → p1) ∨ p2) ∧ True)) ∧ ((p4 ∧ ((False ∧ p3) → True)) ∨ False)) → ((False ∧ p4) ∨ (((p4 ∧ False) ∨ True) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179245218149227199202129273356 : ((p5 ∧ ((False ∨ ((p5 ∧ p5) ∨ ((False ∨ p1) → True))) → (False ∨ p3))) ∨ ((False ∨ (True → (p2 ∨ (((p1 → p2) ∧ p4) ∧ False)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599592005050569719462866005631 : (((((p5 ∨ p1) ∨ (((((False ∨ (p2 ∨ ((p1 ∧ p4) ∧ (False → False)))) ∨ p4) ∨ (p5 → p2)) → p4) ∨ ((p5 ∧ p2) ∨ True))) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178486285765479080060251870088 : (((((p3 ∨ True) ∧ False) ∧ (p3 → (p1 → True))) ∨ ((p5 → p1) → False)) ∨ (True ∨ (True ∧ ((((p2 ∧ True) ∨ (p5 ∧ p5)) ∧ True) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660158469438046131417326153944 : (((((((((p2 ∨ p4) ∧ p5) → (p2 ∨ p4)) ∧ p5) ∧ (False → (p2 ∨ (True ∧ ((p2 ∧ (p4 ∨ p5)) → False))))) ∨ p4) → (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636006768513295035320750603695 : (((((((((True → p4) ∨ p5) ∨ p3) ∨ p4) ∧ ((False ∨ (p3 → (p1 → p3))) → p3)) ∧ (p5 ∨ ((True → (p3 ∧ False)) ∨ p3))) → p3) ∨ p4) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h9 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h10 : (False ∨ (p3 → (p1 → p3))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- Implications on the right can always be decomposed.
            intro h12
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h13 := h5 h10
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
            have h16 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h15, we can now drive its conclusion.
            let h17 := h15 h16
            -- We need to get the right conjuct of h17 based on <expert-advice>.
            let h18 := h17.right
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h21 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h22 : (False ∨ (p3 → (p1 → p3))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- Implications on the right can always be decomposed.
            intro h24
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h25 := h5 h22
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
            have h28 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h27, we can now drive its conclusion.
            let h29 := h27 h28
            -- We need to get the right conjuct of h29 based on <expert-advice>.
            let h30 := h29.right
            -- False on the left can always be used.
            apply False.elim h30
          case inr h31 =>
            -- One of the premise coincides with the conclusion.
            exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h36
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h38 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h39 : (False ∨ (p3 → (p1 → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h42 := h5 h39
      -- One of the premise coincides with the conclusion.
      exact h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h46 := h44 h45
        -- We need to get the right conjuct of h46 based on <expert-advice>.
        let h47 := h46.right
        -- False on the left can always be used.
        apply False.elim h47
      case inr h48 =>
        -- One of the premise coincides with the conclusion.
        exact h48
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43054959302316463891123432131 : ((((((((p4 → ((p1 ∧ p5) → p1)) ∧ p4) ∧ (((True ∨ (p4 ∧ p4)) → (p4 ∨ (p1 ∨ p1))) ∧ p4)) → p3) → p2) ∧ p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2563205954314934022611819818 : ((p3 ∧ (((p2 ∨ p3) ∧ (p4 ∨ False)) ∨ p4)) ∨ ((p3 ∧ (p3 ∧ True)) → ((p5 ∨ (((p3 → (True ∧ p3)) → False) → p4)) ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → (True ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735801780805545503438657847033 : ((((p5 ∨ p5) ∧ ((p1 ∨ ((p3 → ((True ∨ ((p4 ∨ p2) ∧ p3)) → p5)) → p4)) ∨ ((((False ∧ (p2 ∨ True)) ∧ p2) ∨ p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217005785255344899750203255105 : ((((True ∧ p5) ∧ p4) ∨ False) → (((True ∧ (((p2 → p4) ∧ (((False ∧ (p2 → p4)) → True) ∧ p3)) ∧ p2)) → False) ∨ (p1 → (p2 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156816114256146776141596081694 : (((p2 ∨ (p1 ∧ ((p2 ∨ p5) ∨ ((p5 ∧ True) ∧ (((False ∧ p3) ∨ (p2 ∨ False)) → p2))))) ∧ p3) ∨ ((p5 ∧ p1) → (p2 ∨ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161628163311577547733632992751 : ((False ∨ (p2 ∧ (((((p2 ∧ (p2 ∨ p3)) ∧ (p2 ∨ p4)) ∧ p4) → ((p5 ∨ p3) → False)) → False))) → (((p1 → False) ∧ (p1 ∧ p2)) → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53847960258053642152293979144 : ((((p4 ∨ (p3 ∨ (False → False))) → ((p3 ∨ p4) ∧ p3)) ∨ (((p5 ∨ ((p3 → (p1 → (p3 → p1))) ∨ p5)) ∨ (False → p1)) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185286148919252570090567588708 : ((p2 ∧ ((p5 → ((False ∨ (False ∧ p1)) ∨ p2)) ∧ (True → p1))) ∨ (((p1 ∧ (False ∧ False)) ∧ (p5 ∧ p2)) → ((p3 → p5) ∨ (p4 ∧ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118582030959716185070247751335 : ((p4 ∨ ((p3 → (((p3 → p4) → p3) → (False ∨ ((True ∨ ((p2 ∧ False) ∨ ((False ∧ p4) ∧ p1))) → (p1 → False))))) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50768939436161067828319327288 : (((False ∨ (p5 ∨ ((((p1 ∨ False) → (p1 ∨ p5)) ∨ ((False → p3) ∨ (True ∧ True))) → (p3 ∨ p5)))) → ((p4 ∨ False) ∧ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44118683195967219937911457924 : ((((((p2 ∧ p1) → ((False → ((False ∧ p3) ∨ p3)) ∧ (True ∨ p2))) → (((p3 → p3) ∧ p3) ∨ False)) ∨ (p5 ∧ (p5 ∨ True))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615537725044884896304018833984 : (((((((p4 → (p5 ∨ p3)) → p1) ∧ (p4 ∧ ((True ∧ ((p2 ∨ p5) → p4)) ∨ p5))) → (p4 ∧ ((p1 ∧ (p1 ∨ p5)) ∧ False))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_134306694594767885930829256272 : (((True ∧ ((p3 → ((p3 ∨ (p1 → (p5 ∧ (p5 ∧ ((False ∧ True) ∨ ((p1 → p5) ∨ p2)))))) → False)) → False)) ∨ False) ∨ ((True ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149782098451616952833854239858 : ((False ∨ ((p2 ∧ ((False → ((p3 ∨ (p1 ∧ True)) ∧ ((p2 ∨ True) ∨ p5))) ∨ (p5 → p4))) → (p4 → p3))) ∨ (p2 → (p3 → (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121420087365571683250881789983 : ((((p2 ∨ (p3 ∨ ((((((p4 → True) → p4) ∧ (p4 ∨ False)) ∧ (p2 → True)) ∨ True) ∧ (p4 ∨ (True ∨ p3))))) ∨ p4) → p1) → (True → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ (p3 ∨ ((((((p4 → True) → p4) ∧ (p4 ∨ False)) ∧ (p2 → True)) ∨ True) ∧ (p4 ∨ (True ∨ p3))))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_52094412892127972550689182944 : (((((True → (False ∨ ((p4 ∧ (True → True)) → p4))) → (p2 ∧ (p1 → p2))) ∨ p1) → ((True ∧ (True ∧ p2)) → (p1 ∧ (False ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317740522612619078391956100711 : (p4 ∨ ((((p5 ∧ (False → (p4 → True))) → ((((True ∧ p1) ∨ p2) ∨ p1) ∧ (False ∨ ((p4 ∨ p1) → False)))) → (p5 ∧ (False ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66305230337408137577720776635 : ((p5 ∨ ((p4 ∧ p1) → (p3 ∨ (((((p1 → p1) ∧ ((True ∨ (True ∨ p1)) ∧ ((p2 ∧ p5) → p1))) → p1) → p5) ∨ (p5 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724584178169523681967625755941 : ((((p1 ∨ (p5 ∧ p5)) ∧ (p5 ∨ (((p2 ∨ p2) ∨ True) ∨ (True → ((((p2 → p2) ∧ p5) ∨ p3) ∧ (p5 ∧ (p3 ∧ (p1 ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324081887793654559232789197812 : (p5 ∨ (((p3 → ((p4 ∨ p5) → (False ∧ False))) → ((p2 ∧ p3) ∧ p4)) ∨ ((False → p3) → ((True → p1) ∨ (((True ∨ p5) ∨ p1) ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698746421614916090048221039444 : (((((p5 ∧ p3) ∨ (((True → (p4 ∧ p5)) → (p1 ∧ False)) → p5)) ∨ ((((True → p4) → p1) → p4) ∧ (((p3 ∧ p1) → True) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47148285313999306950004641526 : ((((((True ∨ False) ∧ p2) ∨ (p5 ∨ (p1 ∨ (((p4 → (False ∧ p5)) → p2) ∧ p3)))) ∨ (p4 ∨ ((False ∨ False) → p4))) ∨ (p1 ∨ p2)) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672106307707798530228337625019 : ((((((p5 ∧ (p5 → p5)) ∨ (((p2 ∨ p4) ∨ (p2 ∧ p3)) ∨ (((True ∨ p1) ∨ (p5 ∨ p2)) ∧ False))) ∨ False) → ((p4 ∧ p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627646492551096140061375735873 : (((((((p3 → (p4 ∧ ((p5 ∧ p5) ∧ (((True ∨ p2) → (True → p5)) ∧ (p4 ∨ True))))) → True) ∧ (p2 ∧ (p1 → p2))) ∧ p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201194844030242401253247971760 : ((p1 → (p4 ∧ ((True ∨ (p4 → p2)) ∨ p1))) → (p2 → ((p1 ∨ (p3 → (p1 → p3))) ∧ (p5 → ((p3 ∧ p2) ∨ (False → (p4 ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730649683154659302089852073998 : ((((p2 ∧ (p5 → True)) → (((((p4 ∨ (p3 ∨ p2)) → p3) ∨ (((False ∧ (p4 ∨ p3)) ∧ True) ∨ ((True ∧ p5) → False))) ∨ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45271227142001014180757660475 : (((p2 ∧ ((p3 ∧ (p3 → ((((p2 → (True ∧ ((p5 → p4) ∧ (p1 ∨ p2)))) → p2) ∨ p5) ∨ (p2 ∧ (False ∨ p5))))) ∨ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18103664972911623651576003519 : (((True → ((p5 ∨ (False ∧ (((p2 → ((False ∧ p2) ∧ p1)) ∧ (p5 ∨ p2)) ∨ (True → p5)))) ∧ p4)) ∨ ((p3 → p1) ∨ (True ∨ p3))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606450524813531955454234545754 : ((((((p2 ∨ (p4 ∧ (p1 → (p1 ∧ (((((p5 ∧ p4) → (False ∨ p2)) ∨ (p5 ∧ p3)) → (p3 → p5)) ∧ p5))))) ∨ True) ∧ p5) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_52193929682377587076308781312 : ((((p2 → (p1 → p2)) ∧ (False → (p5 ∧ ((p1 → p5) → (p5 ∧ (False → True)))))) → (((p1 → (p5 ∨ p4)) ∧ p5) → (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158313051567452510162096773087 : (((False ∨ (p5 ∧ True)) → (p1 ∨ (p2 ∧ ((p4 ∨ False) ∧ ((p4 → (p1 ∧ p3)) → (p3 → False)))))) ∨ ((((p4 → p3) → p3) ∧ False) → p4)) := by
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
theorem thm_5_vars_305577470965313251398480177535 : (p1 ∨ (((((p4 ∨ p2) ∨ p2) ∧ (True ∧ (p2 ∨ (p1 ∧ False)))) ∧ True) ∨ ((p1 → True) ∨ ((p2 ∨ (True ∨ ((p3 ∨ p5) ∧ p2))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67694206697109089729143737953 : ((p1 → (p3 → (p1 ∧ (p1 ∧ (((p1 → (p1 ∧ (((p4 ∧ p1) → p1) → (p5 → (p4 ∨ p1))))) → p3) → (p5 ∧ (p4 → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136426710822765832291316137805 : (((((p2 → p5) ∨ False) → p4) → (((p5 ∧ (p4 ∨ p1)) → p3) ∨ (False ∧ ((p4 ∨ p2) ∨ (p3 ∨ (p1 ∧ False)))))) ∨ (p1 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55747833054988070550277195402 : ((((False ∨ (p1 ∧ p4)) → p5) ∧ ((p4 → ((((((p1 ∨ False) ∧ p3) ∨ ((p2 ∧ True) ∨ p5)) ∨ p5) → p3) ∨ p4)) ∧ (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76676623689932743445676615709 : ((((((False ∧ ((True ∨ False) → p4)) ∧ (p1 ∧ (p1 ∨ p3))) ∨ (True → (p2 ∧ True))) ∨ (((p4 → (False ∧ p1)) ∧ False) → True)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∧ ((True ∨ False) → p4)) ∧ (p1 ∧ (p1 ∨ p3))) ∨ (True → (p2 ∧ True))) ∨ (((p4 → (False ∧ p1)) ∧ False) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226185202817853854800039386957 : (((p1 ∨ p4) ∨ p5) ∨ (p1 → (((p5 ∨ False) ∧ p1) → (((p2 ∧ p1) ∨ (p2 ∨ ((p2 → (p3 → (False → (p4 ∨ p5)))) ∨ p4))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793541933327491358614352574497 : (((True → (p2 ∨ ((p3 ∧ (p4 ∨ ((((p2 ∨ p5) ∨ True) ∨ ((p4 ∨ (False → p3)) ∧ (False ∧ p4))) ∧ p4))) ∨ (True ∧ (p4 → True))))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181710427419185851826037948284 : ((p5 → ((p5 ∧ True) → (p1 ∧ (((p1 ∨ (p3 ∨ p1)) ∨ False) → p4)))) → ((True ∧ ((True → (p5 ∧ (p5 → p2))) ∧ p4)) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193633434014566491386090203305 : ((True ∧ (p5 ∧ ((((p4 ∨ p5) ∧ p4) → p1) → p2))) → ((((((p5 → p1) ∨ p3) → False) ∧ p2) ∨ p3) ∨ (((p1 → p2) ∧ False) → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134165593096061075011689435592 : (((((p5 ∨ (True ∧ (p2 → p4))) → ((True ∨ ((p4 → p3) ∧ p1)) → False)) ∧ ((p4 ∨ p1) → (p2 ∧ p3))) ∨ p4) ∨ (p3 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192589974711019429740644315518 : (((p2 → ((p1 ∨ p4) ∨ (p4 ∧ (p1 ∨ p4)))) ∨ p1) → ((((p4 ∨ p1) ∨ False) ∨ (((p4 → p5) ∧ False) ∧ (p5 ∧ p4))) ∨ (p4 ∨ True))) := by
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
theorem thm_5_vars_50714273742584635905965904836 : ((((p5 ∧ p5) ∨ (((p2 ∧ ((p5 → p3) → (p4 ∧ (p3 ∨ (p3 → (p2 ∧ p3)))))) ∨ p2) ∧ True)) → (p5 ∧ ((p4 ∧ p4) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300816756753362779586606263597 : (False ∨ ((((((False → p3) ∨ p3) ∧ p1) ∧ p1) ∧ ((p2 ∨ (False → (p2 ∨ p3))) → p2)) → ((p3 ∧ ((p4 ∧ p4) ∨ (p3 ∨ False))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ (False → (p2 ∨ p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h17 := h9 h15
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h19 : (p2 ∨ (False → (p2 ∨ p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h21 := h9 h19
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h31 : (p2 ∨ (False → (p2 ∨ p3))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- False on the left can always be used.
          apply False.elim h32
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h33 := h25 h31
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h35 : (p2 ∨ (False → (p2 ∨ p3))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h36
          -- False on the left can always be used.
          apply False.elim h36
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h37 := h25 h35
        -- One of the premise coincides with the conclusion.
        exact h37
    case inr h38 =>
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240447396076684279327664429106 : ((p5 ∨ True) ∧ ((p2 ∨ (p4 → ((((p4 → True) → p2) ∧ True) ∨ p2))) ∨ (((False ∨ p1) ∨ p3) ∨ ((p5 → True) ∨ ((p1 ∧ p5) → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231554608984826525812039901061 : (((p5 → False) ∨ p5) → ((((True → ((False ∨ (p5 ∧ True)) ∨ ((p3 ∨ ((True ∧ (p4 ∧ p4)) → False)) ∧ (p1 ∨ False)))) → False) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193384529689439849521598219539 : (((True ∧ p5) ∧ (((p2 → (p2 ∨ p5)) → p3) ∨ p5)) → (((p5 ∨ ((p2 ∧ False) ∨ True)) → (p2 ∧ (((p1 ∨ p2) ∧ p2) → True))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p5 ∨ ((p2 ∧ False) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p5 ∨ ((p2 ∧ False) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135316463323807487333358829534 : ((((p2 ∧ (False ∧ (p5 → (False ∧ ((p1 ∧ ((p5 ∨ p3) → True)) ∨ p1))))) ∨ (True → True)) ∧ ((True ∨ p4) ∨ p4)) ∨ ((p1 ∨ p1) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190508980081596724393705574296 : ((((p2 → (((p1 → p2) ∨ p2) → p1)) ∨ True) → p2) ∨ (True ∨ ((((False ∨ p5) ∨ ((p3 ∧ (p5 ∧ p1)) ∧ True)) ∨ (True ∨ False)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179338242565610418541909462290 : ((p1 ∨ (((p1 → False) ∨ p1) → ((False ∨ p5) ∨ (p2 ∨ (p2 ∧ p1))))) ∨ (False → (((p5 ∧ ((p3 ∧ True) ∧ True)) ∧ (p1 ∧ p2)) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h4.left
  let h12 := h4.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46308217054178016391128820285 : (((((True → (((True ∧ ((p5 → (False ∨ (p2 → True))) ∧ p3)) ∨ False) → p2)) ∧ p5) ∧ (p3 ∨ (True ∧ (p2 ∨ True)))) ∧ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61181789027921452768246439742 : ((False ∧ ((p4 ∧ False) ∧ ((((p2 ∨ True) ∧ ((True → (p5 ∧ False)) ∨ p1)) ∧ (p2 → p2)) → ((True ∨ p3) ∧ (p2 ∨ (True → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49213001460002860164090685979 : ((((p3 ∧ True) ∧ (((p4 → p4) ∨ False) → ((p4 ∧ p4) ∨ (p5 → ((p1 ∨ (False ∨ (p5 ∨ False))) → p3))))) ∨ (p2 ∧ (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166564757073783182082646156101 : ((p5 ∨ (p5 ∨ ((p1 → p5) → (p1 → (((False → False) → p3) → ((p5 ∧ p5) ∨ p5)))))) ∨ (((p3 ∨ ((p1 ∧ p5) ∨ True)) ∧ p2) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



