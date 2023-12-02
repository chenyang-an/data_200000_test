variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39850575699233862633462660387 : (((p1 → ((p1 ∨ p4) ∧ ((((p5 → (p2 → ((p5 → p3) ∨ p5))) → p1) ∨ (((p4 ∧ p1) ∧ p5) ∨ p1)) → (p2 ∧ p5)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734466535007941162727811884723 : ((((p1 ∨ True) ∧ ((((p3 ∧ (p3 ∧ p2)) → p3) → False) → (p3 ∧ (p4 ∨ (False ∨ ((p4 ∧ ((p3 → p4) ∧ (p1 → False))) ∨ p2)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p3 ∧ p2)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p3 ∧ (p3 ∧ p2)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64950181204456160304378952573 : ((p2 ∨ (((p4 ∧ (p3 ∨ ((True ∨ (p4 → p5)) → p4))) ∨ p1) → ((p1 → (p2 ∧ p2)) ∧ ((True ∨ False) → (p5 ∨ (p5 ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442496444262197676835275056041 : (((((((((p5 ∧ (p2 → (p5 ∧ p1))) ∨ p2) ∧ (p1 ∨ (p4 ∨ False))) ∨ ((p3 ∧ True) → p1)) ∨ p4) → p3) ∨ ((False ∧ p2) → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157757164508441595492669006418 : ((((False ∧ False) ∧ ((p4 ∧ ((False ∧ p4) ∨ (p5 ∨ p1))) ∨ p2)) ∧ ((p5 → (p1 ∨ p2)) ∧ p2)) ∨ (False ∨ (((p4 → p4) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149850468230773826762656006867 : ((p1 ∨ (False ∨ (((((p4 ∨ (p4 → False)) ∨ p1) → ((p5 ∨ True) → p2)) ∨ (p3 ∨ (p2 → p2))) ∨ p1))) ∨ (((False → False) ∨ False) ∧ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631498640675042403964597634241 : ((((((((p3 ∧ (False ∨ (p1 → ((False → p1) ∧ (((p4 → p1) → False) ∨ False))))) ∧ p3) ∨ False) ∧ ((True → p2) ∨ p4)) → False) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51357559288403392546633459902 : (((((((p5 ∨ (True ∧ True)) ∧ (False ∧ False)) → p1) ∨ ((p5 → (False → p5)) ∨ p2)) ∧ p3) → (p3 ∧ (p2 → ((True → p1) ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42814203751040995392147150843 : (((p1 → ((((((False ∨ p2) ∧ ((p3 ∨ True) ∧ p3)) ∨ p2) → p5) ∨ ((p2 ∧ (p4 ∨ (False → p5))) → False)) → (False ∧ p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49933730310280133965318636763 : ((((p2 → (p5 ∧ ((((True → (p3 → True)) ∨ (p5 ∧ ((p2 → p4) → p2))) ∨ p1) ∨ p5))) → p2) ∧ (p5 ∨ (p5 ∧ (True ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251572661187055266735633481999 : ((p3 → False) ∨ ((False ∨ True) → ((((((True → True) ∨ False) ∨ p1) → (True ∧ True)) → (((True ∨ p1) ∨ True) → p2)) ∨ ((p5 ∨ True) ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319555323172902684959620250616 : (p4 ∨ ((p1 ∧ (p5 ∧ (p3 → (p4 ∧ (p1 ∨ (p3 → p4)))))) ∨ ((((p1 → p3) ∨ (False ∨ ((p2 ∧ True) ∧ p4))) ∨ p2) → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46971390054178686274377999480 : ((((((True ∨ ((((p2 ∨ p4) ∨ p5) ∧ (p5 ∨ (False ∧ p4))) ∨ (p3 → True))) ∧ (p4 ∨ (p5 → False))) → p4) → p1) ∨ (False → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118273925893294535836537277009 : ((p1 ∨ ((((p1 → p2) → p2) ∧ True) ∨ ((p3 ∨ p3) ∧ (((False ∧ p5) ∧ p5) ∧ ((p5 → (p1 ∨ p3)) → (p2 → False)))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68692242032551974223004391921 : ((p4 → (((True ∨ ((p3 ∨ False) → (p4 ∨ p5))) → (p4 → ((((p3 ∧ p2) ∨ False) ∨ p2) ∧ ((True → False) → p3)))) ∨ (p3 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206152467362535835600298566233 : ((p5 ∧ ((p1 ∨ (p4 ∨ p1)) ∧ p3)) ∨ ((((True ∨ ((False ∧ (p5 ∧ False)) → True)) ∧ False) → p4) ∨ (p2 → ((p3 → p4) → (p5 → p2))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114687580599236078871970691979 : (((True → (False ∧ ((p1 ∨ p5) → (False ∨ (((p5 → (p5 ∧ p3)) → p3) ∧ p1))))) ∨ (p2 ∨ ((p2 → p4) ∨ (p3 ∧ p1)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43607777967200603563181238534 : ((((((p1 ∨ ((p5 ∨ (((False ∨ p1) ∨ (p5 ∨ True)) ∧ (p1 → (p2 → False)))) ∨ (True ∧ p2))) ∧ (p4 → p3)) → p5) → True) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112035311701174374796653558243 : ((((p5 ∧ (p1 ∧ p1)) ∨ ((p4 ∨ (p2 ∧ (((p3 ∧ (p4 ∧ p5)) → p5) ∧ p4))) ∧ (p5 → (p1 → (p5 → p4))))) ∨ p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46494177061025732811226075846 : (((((p1 → p2) ∨ p2) → (p3 ∨ ((True → (True ∧ p2)) ∨ (p4 ∨ (((((p5 ∨ p5) → p2) → False) ∨ True) → True))))) ∧ (p4 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226703488533539397627008426588 : (((p1 ∧ True) → False) ∨ ((((p4 ∧ (p5 ∧ ((p2 ∨ (p5 ∧ p3)) ∨ p3))) → (p5 → False)) ∧ (p3 ∧ (p5 → (p2 ∨ (p1 → p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741472026029924189942584849262 : ((((p5 ∨ p2) ∨ (((False → p4) → (((p3 → p3) ∧ False) ∨ p5)) → ((((True → (False ∧ (p5 → False))) ∧ True) ∧ (p5 ∨ True)) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607068403289686640602271630547 : ((((((p4 ∧ (((p2 → False) → ((p1 ∨ p5) ∨ p4)) ∧ False)) ∧ (p5 → ((p4 ∧ ((p5 ∧ p2) → (True ∧ p1))) ∨ p1))) ∧ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_205094327629590959059743281378 : ((((p3 ∨ False) ∧ p1) ∧ (p4 → p3)) ∨ ((p4 → ((((p4 ∧ p3) ∨ p5) → p4) ∧ False)) → (True → ((p4 ∨ (False ∧ p3)) → (p5 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165878013636071801299525950703 : ((((False → p2) ∧ p2) → (((p5 ∧ (p4 ∨ p3)) ∧ True) ∧ ((True ∨ (p1 → p5)) ∨ p4))) ∨ (True ∨ (p2 ∧ ((p1 ∨ False) → (p5 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789862322176197765081947837736 : (((p5 ∨ ((False ∧ (False → p3)) ∨ ((((p4 ∧ (p2 → (p2 → p4))) → p3) ∨ (((p4 ∧ p4) ∨ ((p1 → p5) ∧ p3)) → False)) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_147207584593732520465023788558 : (((p1 → ((((False ∧ p1) → p4) → (True ∧ ((p2 ∨ p3) ∨ p4))) ∧ ((p4 ∧ False) ∧ (p3 ∨ False)))) ∧ p1) ∨ (((False → True) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63127275270639510959537993344 : ((p5 ∧ ((((((p2 ∧ (p2 ∨ (p1 ∨ (p1 ∧ p4)))) ∨ (p1 ∧ True)) ∨ p3) ∧ p5) → (True ∨ (((p1 → p5) ∧ p5) → p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690937717956260983554111845205 : ((((((p5 → ((p4 ∧ False) ∨ p5)) → ((p4 ∧ (True → p3)) ∧ p1)) ∨ (p3 ∧ p1)) → (((True → p5) ∨ (p4 → p1)) → (p1 ∨ p5))) ∨ p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h6 := h3 h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p5 → ((p4 ∧ False) ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683892033348907812428522103126 : (((((True → (((p3 ∨ p1) ∧ True) ∧ (((False → p1) ∨ p4) ∧ ((False ∨ False) ∧ p2)))) ∨ False) ∨ (False → (p2 ∨ (p1 ∨ (p1 ∧ p2))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49710786217234554752169285386 : ((((p5 → p5) → ((p5 ∧ (((p3 → p5) → p3) ∧ (((False ∨ (True → (True ∨ False))) → False) ∧ p1))) → p2)) → ((p4 ∨ p3) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41347583515618336259481608066 : ((((False ∧ ((p5 ∨ (p5 ∨ (p1 ∧ p5))) ∧ ((((False → p4) → p3) → True) ∨ True))) ∨ (((p3 → p2) ∨ p3) → (p4 ∧ False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51294117624762660223969426257 : (((p5 ∧ ((p5 ∧ (p3 ∨ p5)) ∨ (((p2 → ((p4 ∨ p5) ∨ False)) ∨ p4) ∨ (p1 ∨ p5)))) ∨ ((p3 → (True → (p2 ∨ p2))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721297335689570714196186176098 : (((((p1 → p4) → (p2 ∧ p2)) → ((((((p2 → p3) ∨ False) ∧ (p2 ∨ (p3 ∨ (p3 ∨ p2)))) ∧ False) → (True ∨ p5)) → (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158938999854923286269572573085 : ((p2 ∨ (((p2 → False) ∧ (p5 ∧ ((((p4 ∧ (p5 ∧ False)) ∨ False) ∨ False) ∨ False))) ∧ (p3 ∨ p4))) ∨ (True ∨ ((p3 → (False ∧ False)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337120423089358117794146985850 : (p1 → ((False ∧ ((((((p5 ∨ (p2 ∧ p4)) → p1) ∧ (((p5 → True) ∧ True) ∧ p3)) ∧ (p1 ∨ (p4 ∧ False))) → p2) ∧ False)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65743619205809219807390839685 : ((p4 ∨ ((p4 ∧ (p5 → (p1 → ((((((True ∧ p1) ∨ True) ∧ False) → (True ∨ (p4 ∨ True))) → True) → False)))) ∨ (p1 ∨ (p3 → p3)))) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206499779485274138219073212661 : ((p5 ∨ ((p5 → False) ∨ (p4 ∨ p5))) ∨ ((p4 ∧ ((True ∨ ((p3 → p1) ∧ True)) → ((p3 ∧ p1) → (p2 → p3)))) ∨ (False ∨ (False → p4)))) := by
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
theorem thm_5_vars_234064359488334600177373706773 : ((True → (True ∧ False)) → (((p2 ∨ ((p1 ∧ (p2 → (p2 → False))) ∧ (((False ∨ False) → p1) ∧ p3))) ∨ (p3 → p3)) → ((p5 ∧ p3) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h29.left
      let h33 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h34 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h35 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h36 := h1 h35
    -- We need to get the right conjuct of h36 based on <expert-advice>.
    let h37 := h36.right
    -- False on the left can always be used.
    apply False.elim h37
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h40 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h41 := h1 h40
      -- We need to get the right conjuct of h41 based on <expert-advice>.
      let h42 := h41.right
      -- False on the left can always be used.
      apply False.elim h42
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h45.left
      let h49 := h45.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h51 := h1 h50
      -- We need to get the right conjuct of h51 based on <expert-advice>.
      let h52 := h51.right
      -- False on the left can always be used.
      apply False.elim h52
  case inr h53 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h54 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h55 := h1 h54
    -- We need to get the right conjuct of h55 based on <expert-advice>.
    let h56 := h55.right
    -- False on the left can always be used.
    apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165008982789722325123932790933 : (((((False → True) → ((p1 ∨ p3) → p3)) ∨ (p5 ∧ ((p4 ∨ (True → False)) ∨ p1))) → p4) ∨ (((True → ((True ∧ p2) → p5)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37955908271944465075527309545 : (((((p2 ∨ (((True ∨ p1) ∨ p4) ∨ ((p3 → p1) ∧ (((p1 → ((p1 → p5) ∧ p4)) ∨ p1) → p5)))) ∧ p2) ∨ (False ∨ p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39985588092140708301342379405 : (((p5 → ((p4 ∨ (True → (((p4 ∨ ((True ∨ (((p1 ∧ p5) ∨ True) ∧ False)) ∨ True)) ∧ ((True ∨ p1) ∧ p3)) ∨ p1))) ∧ False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55685829536595109155270726144 : (((((p5 ∨ False) ∨ p4) ∨ True) ∧ (((p2 ∨ False) ∧ p1) ∧ ((p3 → (p3 ∨ (p1 ∨ False))) → (True ∧ (((p5 → p5) ∧ p3) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702934855140711492446265003641 : (((((p4 ∨ (False → p4)) ∧ (p3 ∨ ((p2 ∨ p5) ∧ p4))) ∨ ((p5 ∧ True) → ((True ∨ p3) ∧ (p4 → (((p5 ∨ p2) ∨ p4) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187767457520239576164517260481 : ((p2 → (True ∨ (p5 → ((p2 → (p5 ∨ p1)) ∨ (p1 → p1))))) → ((p1 → (p1 ∧ ((p3 → (p3 → False)) ∨ ((p1 ∨ p2) ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181694038000274150059647578532 : ((p5 → ((((p3 → p2) ∧ (True → ((p5 → p5) → p2))) ∧ p5) ∨ False)) → ((False → ((False → p2) ∧ False)) → (((p4 → p3) ∧ p4) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165131639271638654315509511287 : (((((((True ∧ p4) ∨ p4) ∧ (p1 → p1)) ∧ ((p5 ∨ p2) → p4)) ∨ False) ∧ (p3 ∧ p5)) ∨ (((p3 ∧ False) → ((False ∧ p3) ∧ p2)) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51119519044944412722540830954 : (((((((((p4 ∧ p3) ∧ p3) ∧ p2) → p2) → (True ∧ p3)) ∧ ((p3 ∧ False) ∨ p2)) ∨ p2) ∨ (False → (True ∧ (p1 ∧ (False ∧ p4))))) ∨ p3) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349119354028826649133319873513 : (p3 → (True → (((p3 → True) → (p3 ∧ p3)) ∧ ((((p4 ∧ ((p2 → False) → False)) → ((p2 ∧ (p4 ∧ p5)) ∧ False)) ∨ (p3 → p3)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42409910499313087881806560184 : (((p5 ∧ ((p4 ∧ ((True → ((p1 ∧ (p2 ∨ False)) → (p4 ∧ False))) ∧ ((((p4 → p5) → p1) → p5) → (False → p2)))) ∧ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192174910403924714225450457395 : ((((((True → p1) → (p1 → p4)) ∧ p1) ∨ p2) ∧ p1) → (((p3 ∧ p4) ∨ (((p2 → (p4 → ((p2 → p2) → False))) → p5) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748249721703902373816777780374 : ((((p2 → True) → (True ∧ (((True → (True ∧ (((p3 ∨ (((True ∧ p1) ∧ (p5 ∧ p5)) → (p5 ∧ p1))) ∨ True) ∨ p3))) ∨ True) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226278970534709939804995574804 : (((p4 ∨ False) ∨ p3) ∨ ((False ∧ p3) ∨ (False → ((((((p3 ∨ p1) → p1) → ((True → (p2 ∨ True)) ∧ (p4 ∨ False))) ∨ False) ∨ False) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793288439038133863851204669855 : (((True → (p2 ∧ (p1 → (p1 → (((p4 → (p1 ∧ (((p4 → ((False → True) ∧ p5)) → (p3 ∨ p3)) ∧ False))) ∧ p3) ∧ (False → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54437856224521130329872856862 : ((((p4 ∨ ((p3 ∨ p5) ∧ (True ∨ p4))) ∨ p1) ∨ (((False → (p5 ∨ p3)) → ((p5 → (p5 ∨ (p2 → (p1 ∨ p4)))) ∧ p1)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123286417760550088355094685474 : ((((((((p4 → p5) → ((True ∨ p4) → False)) ∧ p2) ∨ (False ∧ p4)) → (False ∧ p2)) ∧ False) ∨ ((p1 ∨ (p1 ∨ True)) → p4)) → (p4 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 ∨ (p1 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746172945708014327994039541762 : ((((p1 ∨ p2) → (p3 → ((((p2 → p2) → (((False ∧ (((False → p5) ∧ p2) ∧ p2)) ∧ p3) → (p2 ∧ (p2 → p3)))) → p5) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1974810549632735093508556684 : ((False ∨ (((((True → ((p5 ∨ p4) → (p2 ∨ p4))) ∨ False) ∨ (p5 → (p1 ∧ p4))) ∧ True) → p4)) ∨ ((p5 → True) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119146005093031408977615149839 : ((p1 → (p2 → (p4 → ((((True ∧ p2) → ((p5 → (True ∨ ((p3 ∨ p2) ∧ ((p3 ∨ p1) ∨ p4)))) ∧ False)) → p5) ∨ p3)))) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43706976515826640597920512124 : ((((((p2 → (True → p2)) ∧ p3) ∨ (((False ∧ (p2 ∧ p4)) ∨ p3) ∧ (((p4 ∧ p2) ∧ (True → (p5 ∧ True))) ∧ True))) → p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354667935189644387759183164897 : (p5 → (((p5 ∧ ((False ∨ ((((p1 ∨ ((False ∧ (p3 ∨ p2)) ∨ True)) ∨ True) ∧ (((p3 → p4) ∨ p5) ∧ p5)) ∨ p1)) ∧ p5)) → p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612177990193371893013260950580 : (((((((p5 ∨ (p5 ∨ (p5 ∨ p5))) ∧ (p3 ∨ p1)) ∨ (((True → (p5 ∨ p1)) → p3) ∧ (p1 ∨ (True ∨ False)))) ∧ (p5 ∧ False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_318284577370615991862476526464 : (p4 ∨ (((p1 ∧ False) ∨ (False ∨ (((p3 → p5) ∧ ((False ∨ ((True ∨ p1) → False)) ∧ ((True → (p2 → p5)) ∧ (p3 ∧ p5)))) ∧ p3))) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h20 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h21 := h15 h20
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305007086647809582434954044342 : (p1 ∨ (((p2 ∧ (p5 → (((False ∧ p1) ∧ False) ∧ (True → p5)))) ∨ (p5 → (p5 → (False ∧ ((p1 ∧ p5) → p2))))) ∨ (p5 → (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209349915979405025747186676252 : ((False → (True ∨ ((True ∨ p4) ∧ True))) → (((p2 ∨ True) → p4) → ((((False ∧ (p3 ∧ p1)) ∨ p2) ∧ ((p4 ∨ p2) ∧ p3)) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_3257043130859385116656872735 : ((True → p5) ∨ ((False ∧ (((p5 → True) → p3) → (False ∧ (p2 ∨ p5)))) ∨ ((p2 ∨ ((True ∧ False) ∧ p1)) → (p2 ∨ (p4 → p3))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253908146901677148083294654157 : ((p1 ∧ p4) → ((p2 ∧ ((p5 → ((p3 ∧ (p2 → ((False ∨ p2) ∧ ((p4 ∧ (p5 → p3)) ∧ ((p5 → p5) ∨ p5))))) → p5)) → p5)) ∨ True)) := by
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
theorem thm_5_vars_204656879660853938368430398185 : (((p4 ∧ ((p3 → False) ∧ p1)) ∨ p3) ∨ ((True → False) → ((((p3 → (((p4 ∧ p2) ∨ p4) ∨ (p5 ∧ p2))) ∨ p2) ∨ p3) ∨ (p4 ∧ p5)))) := by
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
theorem thm_5_vars_154143862799810379895932581377 : (((((p2 ∧ (p2 ∨ (True ∧ (p3 ∨ p3)))) ∨ ((p4 ∧ (p2 ∧ p2)) ∨ (p4 ∧ p5))) ∨ p4) ∨ True) ∧ ((((p5 → p1) ∧ False) → False) ∨ True)) := by
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
theorem thm_5_vars_310453189922930844782526306800 : (p2 ∨ (((p5 ∨ (p1 → (False → p3))) ∨ True) ∧ (p3 ∨ (((p3 ∨ True) ∧ (((False ∨ (p1 → (p3 ∨ p1))) ∨ (p5 → False)) → False)) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∨ (p1 → (p3 ∨ p1))) ∨ (p5 → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : ((False ∨ (p1 → (p3 ∨ p1))) ∨ (p5 → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171361098365921736908214098546 : ((((True → (((p4 → (p4 → p2)) ∧ (p3 ∧ p3)) → False)) ∧ (False → p5)) ∧ p3) ∨ ((p3 → (p3 ∨ (False → (False ∨ p3)))) ∨ (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159179809328973597334528908482 : ((p1 → (p1 ∧ (p4 ∨ ((((p3 ∧ p3) → p2) ∧ ((p5 ∧ p1) ∧ p3)) ∧ ((p5 → p1) → p5))))) ∨ ((p1 ∧ p1) → (p4 → (p4 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206962118387098652798168338595 : ((((p3 ∧ (p3 ∧ False)) → p2) ∧ p1) → ((((p3 ∨ (p4 → p3)) ∨ False) → ((False ∧ ((p4 → p2) ∧ p3)) ∧ (p2 → (p4 ∨ p4)))) ∨ p1)) := by
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
theorem thm_5_vars_731337182050223009748983282010 : ((((p4 ∨ (p3 → False)) → ((True ∧ (((p5 ∨ (p2 → p3)) ∧ (p5 ∨ (True ∨ p4))) ∨ ((p2 ∧ (True → True)) → (True ∨ p3)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256745307193493503780554706526 : ((p1 ∨ p1) → (p4 ∨ (((p4 ∧ ((p3 ∧ p2) ∧ (p1 → (((((p5 → (p4 ∨ False)) → (True → True)) ∧ p5) → True) → p1)))) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_3407561022691536033728373235 : ((p5 → p3) → (p3 ∨ ((False → p1) ∧ (((p3 → p1) → (((False ∨ p1) ∨ ((p1 → ((p5 ∨ p5) → True)) ∨ False)) ∨ True)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230880133643539716716267563709 : (((p2 ∧ True) ∨ p5) → (((p3 ∨ (p1 ∧ False)) ∨ (p3 → (((True → p2) → p5) ∨ True))) ∨ (False ∧ ((p3 ∧ (p5 ∧ (p1 ∧ True))) ∧ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111530290704605604001345629487 : ((((((p1 ∨ (((p4 ∧ ((p4 ∧ (((p4 ∨ (p5 → p1)) ∨ True) → p4)) ∨ False)) ∨ True) ∧ True)) ∧ p3) ∨ p1) ∧ p5) ∨ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112966768368398625929799212380 : (((p1 ∧ ((((p1 → p5) → ((True ∧ (True ∨ True)) ∧ False)) → (p1 ∧ (True → (p5 → ((p4 → False) ∧ True))))) ∧ p5)) → p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221811037485914418843734911296 : (((p2 ∧ p4) → True) ∧ ((p1 → p5) → (p2 ∨ ((((True → p4) ∧ (p5 → (((p3 ∨ ((p3 ∧ p2) ∧ p2)) ∨ False) ∨ p5))) ∨ True) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82202031935658972149344964641 : (((p5 → (p1 ∨ (((p5 → p1) ∨ p3) → ((((p2 → (p5 ∧ p1)) → p4) ∨ (p4 → True)) ∧ (p1 → p5))))) → ((False ∧ p1) ∧ p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p1 ∨ (((p5 → p1) ∨ p3) → ((((p2 → (p5 ∧ p1)) → p4) ∨ (p4 → True)) ∧ (p1 → p5))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66059200210855470786002115792 : ((p5 ∨ ((((p4 ∨ (((p1 ∧ p4) → p2) ∨ ((((p1 ∨ p3) ∨ p5) → (p3 ∨ True)) ∨ p2))) ∨ (p1 → False)) → (p2 → p2)) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56571127370014057895875586414 : (((True → (True ∧ (False → p3))) → (p2 ∨ (((((p4 → (p3 ∨ p2)) ∧ (p1 → p2)) → p3) → (p3 ∧ p3)) ∨ ((True ∧ p4) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171389008473406716862278084858 : (((((True → p2) ∨ ((p3 ∨ p2) ∧ p1)) ∧ (((p5 → p4) ∧ p1) → p3)) ∧ False) ∨ (((p5 ∧ p2) → p1) → ((p3 ∨ p4) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352492707648333204655840913620 : (p4 → ((True → (p1 ∨ p4)) → ((False → True) ∧ ((p2 ∨ (((p3 → True) ∨ (p3 ∧ (False ∨ (p1 → (False ∨ p3))))) → p2)) ∨ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707966378371151734952751528671 : ((((False ∨ (((p4 ∨ (p5 ∨ p2)) ∧ True) ∨ p3)) ∨ ((True ∧ (p2 → (p3 ∨ p1))) → (True ∨ (p3 → ((True ∨ (False → p3)) → p4))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328413315873609235108707398967 : (True → (((((True ∧ True) ∧ p3) ∧ ((p2 ∧ (((p3 ∧ False) ∧ p3) ∨ p4)) → True)) → (True → False)) ∨ ((p1 → (p1 ∧ (p4 ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227589888026371689952046018486 : ((False ∧ (p2 ∧ p4)) ∨ (((p4 ∧ True) ∨ (p1 ∨ False)) ∨ (p2 ∨ ((((p5 → True) ∨ p4) ∨ ((((True → True) ∧ p5) ∨ False) ∧ p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_115573863739798960136172391960 : ((((False ∨ ((p4 ∧ p4) → p2)) → p5) ∧ (p2 → (p4 ∨ (True ∧ ((p3 → (((p2 ∧ p1) → (False ∨ p5)) → p5)) → p4))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345734944672726175357582346405 : (p3 → ((p5 → ((p2 → False) ∨ (((p4 ∨ (((True ∨ False) ∧ (True → (p2 ∧ True))) ∧ (((p4 ∧ p1) ∨ p1) ∨ p4))) → p1) ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684138221601125578211834560161 : (((((((p4 ∨ (((False ∧ p1) ∨ p1) ∧ (p5 ∨ (p2 ∨ p5)))) → p5) ∧ False) ∨ (p1 ∨ p2)) ∨ (((False ∨ (p2 ∧ False)) → True) ∨ p3)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313982248225493837003764023498 : (p3 ∨ (((((p1 ∨ p2) → p2) ∧ (True ∧ p5)) ∧ (True → (True → (False ∧ (((p1 ∧ p3) → (p4 ∧ (p2 ∧ p3))) ∨ p3))))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317707428756139895060442715017 : (p4 ∨ (((((((False → (p4 ∧ p4)) → ((True ∨ p1) ∨ False)) → p5) ∨ p2) ∨ (False ∨ (p1 ∧ ((p1 ∧ p5) → p3)))) ∨ (p2 → p2)) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110595290760149364892926622944 : ((p5 → ((((p3 ∧ p5) ∧ p4) ∧ ((p5 ∧ p5) ∧ ((p5 ∧ ((p1 → p4) ∨ (p1 → p3))) ∨ (p1 ∨ (p2 ∧ True))))) ∨ True)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49165626123280182298753476779 : (((((p4 ∨ (p5 → (False → p3))) → p2) ∨ ((p1 ∨ (((p3 → p1) → (p5 → p4)) ∧ p1)) → (False ∧ True))) ∨ (True ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171659960568531877552608913002 : (((p2 ∧ ((p3 ∧ (True ∨ True)) ∧ (((True ∧ (p3 ∨ True)) ∨ False) ∧ p4))) ∨ p4) ∨ (((False ∧ p3) ∨ ((p5 ∨ (True → False)) → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739037669392092814439752101017 : ((((p3 ∧ p3) ∨ ((p1 → False) ∨ ((((p2 ∨ p5) ∨ False) ∧ ((((p4 ∨ p4) → p3) ∨ p4) ∧ (True ∨ p4))) ∨ (True ∨ (p4 → p3))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344125426659187227008883060311 : (p2 → (False ∨ (((p3 ∧ (p3 ∧ False)) ∨ (False ∨ ((p3 → p3) ∨ (p2 ∨ (True ∧ p5))))) ∨ (p3 ∧ ((p2 → ((True ∧ p3) ∧ p1)) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733085063412435835054350038880 : ((((p3 ∧ True) ∧ ((((p4 ∧ (p4 → p4)) → p1) ∨ ((p1 ∨ ((True → False) ∧ p1)) ∨ p2)) → (p5 ∧ ((p1 ∨ (True → p2)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184606384070343711550657390573 : (((((p2 ∨ p4) ∨ (p3 ∧ p1)) ∨ p3) ∧ (True ∨ (True ∧ p2))) ∨ (((p1 ∧ (p3 ∨ (p4 ∨ p2))) → True) ∨ ((p4 → (p3 ∧ p4)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



