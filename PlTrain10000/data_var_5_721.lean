variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346705263268696027474304411634 : (p3 → ((p2 ∨ ((p4 → p5) ∨ (((p1 ∧ p2) → (True ∨ p1)) ∨ ((False ∧ p2) ∧ (False ∧ ((False ∨ p5) ∧ p2)))))) → (p5 ∨ (False ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- False on the left can always be used.
        apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212864155810495810598684184417 : ((p2 → (p2 → (False → p5))) ∧ (p5 → (((p5 → (((p2 → p4) → p4) ∧ ((p3 → p4) ∧ False))) ∧ ((p1 ∧ p3) ∨ p4)) → (p3 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192646220264505872548565148276 : ((((p4 ∧ ((p2 → p3) → (p4 ∧ p2))) ∨ p4) → False) → ((p4 → (p5 ∧ p3)) ∧ (((True → ((p5 → p5) ∨ p4)) ∨ (p4 → p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∧ ((p2 → p3) → (p4 ∧ p2))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∧ ((p2 → p3) → (p4 ∧ p2))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∧ ((p2 → p3) → (p4 ∧ p2))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117229547393100212527150829527 : ((True ∧ (True ∧ (p2 ∧ (p1 ∨ (((p4 ∧ (p4 → ((p1 ∧ True) ∨ p3))) ∧ p4) ∨ ((p4 ∧ p3) → (p5 ∨ (p1 ∨ p1)))))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184599806708844673880888415550 : (((((p4 → (p1 ∧ True)) ∨ p2) ∧ True) ∧ ((p2 → False) → p2)) ∨ ((p2 ∨ ((False ∨ False) ∨ (((False ∧ p5) → False) ∨ (p5 ∧ False)))) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_519993304447031334548160878479 : ((((p2 ∨ p4) → (p1 ∨ (((((p4 ∧ False) ∨ p4) ∨ ((p4 ∨ p5) ∧ p4)) ∧ (p3 ∧ ((p5 ∨ False) ∨ p4))) ∨ ((True ∨ p1) ∨ p2)))) ∧ True) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238191768469335291396645829296 : ((True ∨ p4) ∧ (((((p2 → False) → ((False ∨ p2) → False)) → ((((True ∨ p2) ∨ (p1 ∧ p2)) → p3) → False)) ∧ True) ∨ ((p4 → p4) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111778282201118253781000913509 : (((((((p5 ∧ (p1 ∧ (p3 ∧ True))) ∨ ((p4 ∨ True) ∧ (((p4 ∧ False) ∧ p3) ∧ p4))) → p4) ∨ p3) ∨ (p5 ∨ p2)) ∨ p4) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134914256884207487296437418179 : ((((((True ∧ p2) ∧ ((((True → (p2 ∨ p3)) → (True ∨ p4)) ∧ p1) → (p5 → False))) → p5) ∨ p3) ∧ (p4 → p5)) ∨ ((p2 ∧ False) → False)) := by
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
theorem thm_5_vars_263159799663791112718358751399 : (True ∧ ((p5 ∧ ((p4 → (((False → p5) ∧ ((False ∧ p3) ∨ p4)) → (p3 ∧ (True ∧ (((p2 ∧ p5) → p1) ∧ p2))))) ∨ p5)) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_68788691860717512271364702534 : ((p4 → (((((p5 → p5) ∧ p1) → False) ∨ True) ∧ (((False ∧ True) ∧ (p1 → False)) ∨ (p5 → (True → (((p4 ∧ p5) → p4) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193253781471108634071339917802 : (((p4 ∧ (p5 → True)) ∧ (p1 ∧ (True → (p3 → False)))) → ((p2 → (((p2 → ((p3 ∧ True) ∨ False)) ∨ True) ∧ p3)) ∨ (p4 ∨ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751229639678005685589267833489 : (((True ∧ ((p1 ∨ (p4 → p5)) → ((((p5 ∨ p5) ∨ (p1 ∨ p4)) ∨ False) ∨ ((((p3 → (True ∨ p3)) ∨ p2) ∨ False) → (p2 → p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119103000398010593306611095342 : ((p1 → ((p5 → ((True ∧ p2) ∨ p4)) → (False ∨ (((((True ∧ (False ∨ p4)) ∧ p1) ∧ p4) ∨ p5) → ((True → p4) ∨ p2))))) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308689597817049303215015869045 : (p2 ∨ ((p1 ∨ (p1 ∨ ((((p3 ∧ p1) ∨ (True ∨ p5)) → (p4 ∧ ((p3 → p5) → True))) → ((p1 → p2) ∨ ((p2 → p1) → p4))))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ p1) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135927531486626951253109616357 : (((True → ((p2 ∧ ((((p3 ∨ False) ∨ p2) ∨ True) → p1)) ∧ p4)) → (p5 → ((p3 ∧ ((p5 → p3) → p5)) ∨ p4))) ∨ ((False ∨ False) → p3)) := by
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
theorem thm_5_vars_616201963611830221809815394161 : (((((p4 ∧ (((p1 ∨ (False ∨ p2)) ∧ (False ∨ (True → True))) ∧ p3)) ∧ ((((p3 ∨ (p1 ∧ (p3 ∧ p4))) ∧ True) ∨ p3) ∨ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962615415445580768289251666252 : ((((True → p5) ∧ ((p5 ∧ p3) → (p1 → (((((p3 ∨ (((False ∨ p1) ∨ p5) → ((p3 ∧ p4) → False))) → p2) ∧ True) ∧ True) ∨ True)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186796421449360286597274114902 : ((((p4 ∧ p1) ∧ (True ∨ p1)) ∧ (((p4 ∨ p1) ∧ p4) ∧ p4)) → (p3 ∨ ((p1 → (p1 → (p3 ∧ (p3 ∧ p1)))) ∨ ((False ∨ p1) ∧ True)))) := by
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
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147473103392391371071342477139 : (((p1 ∧ ((True → (False ∧ p2)) ∨ (p3 → ((True ∧ (((p3 → p2) → (p1 ∧ p4)) ∨ True)) → p1)))) ∨ p4) ∨ (False → (p5 ∧ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56314005010697679244323180255 : ((((True ∨ (p1 ∨ p2)) ∧ p4) → (True ∧ ((((p2 ∨ (True ∧ (((p1 → (p3 ∨ (p3 ∧ p3))) ∧ p1) ∧ p5))) ∧ p2) ∨ p4) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220944610270053293538527533393 : (((p1 ∧ p4) ∨ True) ∧ (((p4 → (((p3 ∨ (True ∧ False)) ∨ p1) ∨ (p5 ∧ (True ∧ (p4 ∧ p1))))) ∨ (((False → p2) ∨ p4) ∨ p5)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47047859085654387604952057015 : ((((p2 ∧ (((p4 → (p5 → p3)) → p3) ∨ ((p3 ∧ p2) → (p1 ∨ ((p2 ∧ p4) ∨ (p5 → p4)))))) ∧ (p3 ∧ p3)) ∨ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919259050257299545274108642546 : ((((((p4 ∨ (p3 ∨ p4)) ∨ p4) ∧ (((False ∨ (True → p1)) ∨ p1) → False)) ∧ ((((p2 → p1) ∨ (True ∧ p3)) → (p5 → True)) → p1)) → p2) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((False ∨ (True → p1)) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : (((p2 → p1) ∨ (True ∧ p3)) → (p5 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h9
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h8
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : ((False ∨ (True → p1)) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h17 : (((p2 → p1) ∨ (True ∧ p3)) → (p5 → True)) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h17
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h21 := h5 h16
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : ((False ∨ (True → p1)) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : (((p2 → p1) ∨ (True ∧ p3)) → (p5 → True)) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h27 := h3 h24
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h28 := h5 h23
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h30 : ((False ∨ (True → p1)) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h31 : (((p2 → p1) ∨ (True ∧ p3)) → (p5 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h34 := h3 h31
      -- One of the premise coincides with the conclusion.
      exact h34
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h35 := h5 h30
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260342448274650617830040458162 : ((p2 → p5) → (((((((((p3 ∨ True) ∨ ((p2 → False) → True)) ∧ (False ∨ True)) ∨ p4) → p5) ∨ p2) ∨ (p4 ∨ (p4 → False))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_404492034787880148171049066877 : ((((((((p2 ∧ (True ∧ ((p4 ∨ ((p1 ∧ (False ∧ False)) ∧ p5)) ∧ (p4 ∧ (p4 ∧ (p5 ∧ p3)))))) → False) → p2) ∨ True) → p3) → p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ (True ∧ ((p4 ∨ ((p1 ∧ (False ∧ False)) ∧ p5)) ∧ (p4 ∧ (p4 ∧ (p5 ∧ p3)))))) → False) → p2) ∨ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337078190529955793343391614949 : (p1 → ((((((((((False ∨ (True ∨ p2)) → p3) → p3) → (p4 ∨ True)) → p4) → p1) → False) ∨ False) ∨ (p2 → (p4 ∧ p2))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342617533831626789103422274391 : (p2 → ((p2 → (p3 → ((p1 ∧ (p5 ∨ p1)) ∨ ((False ∨ p4) → True)))) → ((((True → ((p2 ∨ (p4 ∨ False)) ∧ p1)) ∨ p2) ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185673998891818387687242673471 : ((p1 → (((p4 ∧ p4) → ((True ∨ (p5 ∨ p1)) ∧ p1)) → False)) ∨ (True ∨ ((False ∧ (p5 → (False ∧ ((p4 → p2) ∧ (p1 → p1))))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43037926119494907188688815988 : ((((((p2 ∧ (p4 ∨ (p4 ∨ p4))) ∨ (p3 → ((p4 → ((True → p2) ∧ (p1 ∨ ((False ∧ p5) → p2)))) ∧ p2))) ∨ p3) ∧ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351531534203985250570401354583 : (p4 → (((((((p3 → (p2 ∨ False)) → True) ∨ p5) ∧ p4) → p5) ∨ (((p5 ∧ p1) → p3) ∨ p2)) ∨ (p1 → (((p4 → p5) → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606619029121881453567054094874 : ((((((p5 ∧ ((((p4 ∨ (p2 ∨ False)) → (p5 → ((p1 ∧ True) → False))) → ((p4 ∨ p2) → (False → True))) ∧ p3)) → p1) ∧ p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56465203234817713122090632006 : ((((p5 ∧ True) → (p4 ∨ p1)) → ((((p2 → ((True → p5) → p4)) ∨ (p2 ∧ p4)) ∧ (p4 → (p2 ∨ p5))) ∧ (p2 ∨ (p1 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166279241938972268550447360413 : ((p4 ∧ (((((p1 ∨ (((p4 → p2) ∨ p1) ∨ True)) ∧ True) ∨ (p1 ∨ p4)) ∧ p3) ∨ p1)) ∨ ((p5 ∨ ((p2 ∧ p5) ∨ (p2 ∨ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204637407401837209732430028218 : (((p1 ∧ ((p1 ∧ p1) ∧ p1)) ∨ p3) ∨ (False → ((((p3 ∨ p1) ∨ p5) → ((p1 ∨ p5) → ((p2 ∨ True) → (p4 ∨ p4)))) → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146937517502522293803373802837 : (((((p1 ∨ (((((p3 ∧ p5) → (p1 → (p4 ∧ (p4 ∨ p1)))) ∧ p3) ∧ p5) ∨ False)) ∨ p3) ∨ True) ∧ True) ∨ (False ∧ ((p1 ∨ p1) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134222346205809057905136215906 : ((((((p4 ∧ (p2 ∧ p5)) → p3) → p2) ∨ ((p3 ∧ ((((p5 ∧ p1) ∨ (p2 ∧ True)) → p4) ∧ p2)) ∨ False)) ∨ True) ∨ ((p1 ∧ p1) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787006079447709958560576259176 : (((p4 ∨ ((False → False) ∧ ((p1 ∨ ((p1 ∧ (p4 ∧ p5)) ∨ p1)) ∧ ((p1 ∨ (True ∨ ((p1 ∧ p3) → (p2 ∧ p1)))) ∨ (p1 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317761203768794126721799643257 : (p4 ∨ ((((((True ∧ p5) ∨ (p2 → (p1 ∧ p1))) ∨ (True ∨ (p5 ∨ False))) ∧ (p4 ∧ p5)) ∨ (p2 ∨ (p5 ∨ ((p1 ∧ p5) → p1)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231899601259209254556807187694 : (((False ∨ True) → False) → ((p3 ∨ (True ∨ (False → p3))) ∧ (((False ∧ (False ∨ (p1 → p2))) ∧ (p2 ∧ False)) ∧ ((p2 ∨ p1) ∧ (p1 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60239769391143474407368378257 : (((True → p5) → (((((p4 ∨ ((False → p2) ∨ ((False → (False ∨ p1)) → (False ∧ (p2 ∨ p4))))) ∨ p5) ∧ False) ∧ p4) ∧ (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345415110522366124822801230904 : (p3 → (((((True → p3) ∨ True) → ((p2 ∧ (False → (p4 ∨ p2))) ∧ ((p4 ∨ ((p3 → (p5 ∧ (False ∧ p5))) → True)) ∧ True))) → False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248808131986855860842923591614 : ((p3 ∨ p4) ∨ ((p5 → ((p2 → (p1 ∧ ((p3 ∨ (((((p2 ∧ (p5 ∧ False)) ∧ p1) → p4) → False) ∨ p5)) ∧ True))) ∨ (p5 ∨ p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257883524992830915946050788857 : ((p4 ∨ True) → ((p2 ∧ (True ∧ p4)) ∨ (((p2 ∨ True) ∨ p2) ∨ (((True → False) ∧ (p2 ∨ ((p5 → (p3 ∧ p5)) ∨ (p3 → False)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_64684750173739516105830096195 : ((p1 ∨ (p4 ∨ (p2 ∧ (((p3 ∨ ((p5 → (p4 → True)) ∨ p3)) → ((((((p2 ∨ p2) ∨ True) → p2) ∧ p2) ∨ True) → p2)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258337407380203780707307557713 : ((p5 ∨ False) → (((((p3 ∨ ((p4 → p1) ∧ p4)) → True) → ((((p2 → p5) ∧ (p3 ∨ ((p5 ∧ p1) ∨ p4))) ∨ p4) ∧ p4)) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_40395343015823966751375273353 : (((((p4 ∨ (True ∧ (p4 → (((p1 → (True ∨ p2)) → False) ∨ (True ∨ (p5 → ((p4 ∧ p1) → p4))))))) → (False ∧ True)) ∨ p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37527920546044523834968617000 : ((((p1 ∧ ((((((p2 → (True ∧ ((p4 → p3) → (p5 ∨ p2)))) → (p4 ∧ p4)) ∨ p5) ∧ (p2 → True)) ∨ p5) → p1)) ∨ p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54213399746424640431986864873 : ((((p3 → (p5 ∨ ((p2 ∨ p1) ∨ p3))) ∨ p4) ∧ (((p4 ∧ False) ∨ True) ∨ (False ∨ (False ∨ ((((True ∧ True) ∨ p3) ∧ p3) ∧ p2))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42621021601361232617508724573 : (((p3 ∨ (((((((p2 → p1) ∧ True) ∨ p5) ∧ (True → (p5 → p2))) ∨ False) ∧ False) ∧ (p4 ∨ (((p5 → True) → p1) ∧ p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665631009146235772303720455056 : ((((((p1 ∨ (False ∨ p2)) → (((p3 → (p4 ∨ ((p1 ∨ (p4 ∨ p2)) → False))) ∨ (p2 ∧ p2)) ∧ p1)) ∨ p5) ∧ ((True ∧ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169006556866588986240372772494 : ((p1 → ((p3 → (p2 ∧ p5)) ∧ (p2 → (p2 ∧ (((p4 ∨ p5) ∧ True) → (p4 ∧ p3)))))) → ((((p1 ∨ True) ∨ p1) → (p4 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18783946777977851134936934117 : ((((((p3 ∨ (p2 ∨ p5)) ∧ (p2 ∨ ((p3 ∨ False) ∨ p5))) ∨ (p2 ∧ (p4 → False))) → p1) ∨ ((p2 ∨ (p3 ∨ (p3 ∨ p4))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299750736891872964745317492293 : (False ∨ ((((False → p3) → (p2 ∧ p4)) ∧ (((p3 → p2) → ((False ∧ p5) ∧ (True → (True ∨ p3)))) ∧ ((p3 → (p4 ∨ True)) → True))) → False)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774516570411524753440414230486 : (((False ∨ ((((p5 ∧ (((True → p5) → False) ∨ (p5 → True))) ∨ True) ∧ (p3 → p1)) ∨ (((True ∨ p3) ∧ p4) → (p3 ∨ (p4 ∧ p4))))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321473822993413230332661682944 : (p4 ∨ (p1 → (((((p5 → (p1 → False)) → ((((p1 ∨ p2) → (p4 ∨ ((True ∨ p2) ∨ p5))) ∧ (True → False)) ∨ p1)) ∨ p2) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_147975727365246318208399272340 : ((((((p4 ∨ (False ∨ (p5 ∨ ((True ∨ (p4 ∨ p2)) ∨ p3)))) ∧ (p4 → p4)) ∧ p1) ∧ p1) ∨ (False → p4)) ∨ ((p3 ∧ (p3 ∨ p3)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876249359690283009605462050609 : ((((((((p2 ∧ ((p4 ∨ p3) ∨ (((p1 → p2) ∨ True) → False))) ∨ (p1 ∨ p3)) ∧ (True ∧ p1)) ∨ p3) → (p5 ∨ p5)) ∧ (False ∨ p3)) → p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((((p2 ∧ ((p4 ∨ p3) ∨ (((p1 → p2) ∨ True) → False))) ∨ (p1 ∨ p3)) ∧ (True ∧ p1)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37967917137778735978035284231 : (((((((p2 → False) ∧ ((p1 ∨ p1) ∨ (True ∨ p2))) → ((((p4 → False) ∧ (p5 ∨ p2)) ∨ p4) → p2)) → p2) ∨ (True → p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299126125122884976545485028304 : (False ∨ ((((((((p3 → p2) ∨ p5) ∨ p5) ∨ p3) ∨ (p2 → ((((p2 → ((p5 → p2) → p5)) → False) ∨ False) ∨ True))) ∨ p2) ∨ False) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218339849280494901113462371965 : (((p1 → p1) ∨ (p3 ∨ p3)) → ((p2 ∨ p5) ∨ (p5 → (((p1 ∧ (p1 → (True ∧ ((p3 ∨ (False ∨ True)) ∧ p1)))) ∨ (p2 → True)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47205587329390715651240641292 : ((((((p2 ∨ p4) → ((p1 → p3) ∧ p5)) ∧ (p1 ∨ p2)) ∧ ((p5 → ((p2 ∨ (p1 ∧ p4)) ∨ p1)) ∧ (False → True))) ∨ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808556411960029755718545514826 : (((p4 → (p5 ∨ (False ∨ ((((p3 → p4) ∧ (p4 → (False ∧ p2))) ∧ True) → ((p4 → (p3 ∨ p5)) → ((False ∧ (p1 ∧ p5)) ∨ p4)))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890982436871229725088937374637 : ((((p4 ∨ ((p5 ∧ ((True → p4) ∧ ((p4 ∧ (p3 ∧ p5)) ∨ ((((p4 → p4) → p3) → False) → (p3 ∧ p4))))) ∨ True)) → (p1 ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ ((p5 ∧ ((True → p4) ∧ ((p4 ∧ (p3 ∧ p5)) ∨ ((((p4 → p4) → p3) → False) → (p3 ∧ p4))))) ∨ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114234543927145588718587205056 : (((p4 ∧ ((((p4 → p2) ∨ ((p4 ∨ ((p4 → True) ∧ p4)) ∨ p1)) ∧ (p5 → p3)) ∨ (p4 ∨ p3))) → (p2 → (p2 ∨ p2))) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656973558975198699473818898109 : ((((((True → p2) ∧ (True ∨ p1)) → ((p4 ∨ (p5 ∧ ((p3 → p3) ∧ (p3 ∨ (p3 → ((p3 → p5) ∨ p3)))))) → p5)) ∨ (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249983450901033972549282098240 : ((True → p2) ∨ (((p1 ∨ (p1 ∨ ((p5 ∨ p5) ∧ p4))) ∨ p2) → (p4 ∨ ((p2 ∨ (p3 → (((p5 ∧ True) ∨ p4) ∨ (p1 ∨ p2)))) ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318892033396473065974206573779 : (p4 ∨ ((True ∧ (p3 ∧ (((False ∧ p5) → ((True → p5) ∧ p1)) → (p4 ∨ ((p4 → p1) → (p2 → (False ∧ p2))))))) ∨ (True ∨ (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610741680439031883307502876534 : (((((((True ∧ p1) ∧ (p5 ∨ ((p5 ∧ ((p5 → p1) ∧ (True ∨ True))) ∧ ((p4 ∧ False) ∨ p3)))) → ((p5 → p1) ∨ False)) → p1) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70699222236333912228639698302 : ((((((((p1 ∨ ((p1 ∨ p2) ∧ p3)) ∧ p2) → False) ∧ p1) ∧ ((p3 ∨ True) ∧ p2)) ∧ ((p1 → p1) ∨ ((p2 ∧ p4) ∨ p5))) ∧ p1) → p4) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : ((p1 ∨ ((p1 ∨ p2) ∧ p3)) ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h21 : ((p1 ∨ ((p1 ∨ p2) ∧ p3)) ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h22 := h8 h21
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h25 : ((p1 ∨ ((p1 ∨ p2) ∧ p3)) ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h26 := h8 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h32 : ((p1 ∨ ((p1 ∨ p2) ∧ p3)) ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h33 := h8 h32
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149106856134284773266494077706 : (((p2 → (True → p3)) → (((((True → (p5 → p5)) ∧ True) ∨ (((p2 ∧ p3) → False) → p5)) ∧ True) → p2)) ∨ (p2 → (p5 ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586818459947596165239699918694 : (((((p4 ∧ ((False ∨ (p4 → p3)) → (((False ∧ True) ∨ (True → p4)) ∨ ((p3 ∧ p3) → ((p2 ∧ p4) ∨ (p4 ∨ p5)))))) ∧ p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166674012808248417691522992661 : ((p2 → (((p5 ∨ p4) → (p2 ∧ ((True ∧ ((False ∧ (p1 ∧ True)) ∨ False)) → p4))) → False)) ∨ ((p4 ∧ (p5 ∨ True)) ∨ (p3 → (False → True)))) := by
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
theorem thm_5_vars_153274562821134383372304689492 : ((False ∨ (p5 ∧ (True ∧ (p5 ∨ ((((p4 → p1) ∧ ((p5 ∧ p2) → p5)) ∧ False) → ((False ∨ p3) ∨ False)))))) → (((p3 ∨ p1) ∨ p2) ∨ True)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115458209348354315402560162819 : ((((True ∨ p4) → ((False → (p2 ∨ p3)) → p2)) ∨ ((p2 ∧ p4) ∧ ((p5 ∨ (False → ((p1 ∧ p4) ∧ p1))) → (p2 → p4)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184951465313046266885797085489 : ((((p1 ∨ p5) ∨ p4) → (False ∨ (((p2 → False) ∨ p3) ∨ p1))) ∨ (True ∨ ((p1 ∨ p5) ∨ ((p3 ∨ p2) ∨ ((True ∨ (p2 → p1)) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316713316301144152205796423485 : (p3 ∨ (p5 ∨ (False ∨ (False ∨ ((p5 → p3) ∨ ((((False ∧ (False ∨ True)) ∨ p5) ∨ p5) ∨ (p2 ∨ (p4 → ((p5 ∧ False) ∨ (True ∨ True)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304733785843921110695946721593 : (p1 ∨ (((p2 → ((p4 ∨ (True ∨ (False ∨ False))) ∧ p4)) ∧ ((((p1 → (p1 ∧ (False ∨ (p5 ∨ p5)))) ∨ p2) → p3) → False)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156993145388005608996838122870 : ((((((p2 → True) ∧ True) ∧ True) ∧ (p4 ∧ ((p4 ∧ p4) ∨ ((True → (False ∧ p1)) ∨ False)))) ∨ True) ∨ ((((p1 ∨ False) ∨ p3) → p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251628778786217146263924575879 : ((p3 → p1) ∨ (((p3 ∧ p1) ∧ p2) → ((((False ∨ (p5 ∨ p2)) ∧ (p2 → (((False ∧ (p2 ∨ (p4 ∨ p3))) ∨ p4) ∧ p4))) ∨ True) ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55601271738156507332856531099 : (((True → ((p3 → p5) ∧ (p5 ∨ p3))) → ((((False ∧ (p2 → ((((p2 ∧ p1) ∧ True) ∧ (p3 ∧ False)) ∧ p2))) ∧ False) ∨ True) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708565672618350577830470112960 : ((((((p1 ∧ p1) ∨ ((p2 → p2) ∨ p3)) ∨ p4) → (((p2 ∧ p5) ∧ True) ∨ (p1 ∨ ((p3 ∨ True) ∨ ((p2 ∨ (True → True)) ∨ p4))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218817411915221271913671587868 : ((p1 ∧ (p3 → (p3 → p1))) → (((False ∧ ((((((p5 ∧ (p2 → (False ∧ p2))) ∨ p4) ∧ (p2 ∧ False)) ∧ True) → p5) → p2)) ∧ p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646571907032431274045777160885 : ((((p1 → (((p5 → p1) ∨ p1) → (True → ((((p5 ∧ p3) → (False ∨ (p5 ∨ (p3 ∨ ((p1 ∧ p3) → True))))) → p1) → p2)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114411449703598252608054832101 : (((((p2 ∧ p4) ∨ p5) ∨ (((p4 ∧ (p3 → (p2 → p5))) ∧ p5) ∧ (p2 ∧ (True → False)))) ∨ (p5 ∨ ((p2 → p1) → True))) ∨ (True ∧ p4)) := by
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
theorem thm_5_vars_114928612901936402506027163488 : ((((((True → ((p2 ∨ p5) → p1)) → False) → (True ∨ p1)) → (p1 ∧ True)) → ((((True → p3) ∨ p3) ∨ (p4 ∨ p2)) ∧ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312311807434733452718334047586 : (p2 ∨ (p2 → ((((p5 ∨ False) ∧ ((((False → True) → False) ∨ p5) ∧ p3)) ∨ p2) ∨ ((False ∧ p1) ∨ (p3 → (p1 → ((True ∧ p3) ∨ p3))))))) := by
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
theorem thm_5_vars_65711339294276569066953603082 : ((p4 ∨ (((True → (p3 ∧ (((((p5 ∨ False) ∨ (((True ∧ (p3 → p5)) ∨ p1) ∧ p5)) ∨ p4) → p4) ∨ p5))) ∧ False) ∨ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354579588109197280058486013882 : (p5 → ((((((p3 ∨ True) ∧ (False ∨ False)) → p5) → (p1 ∧ (((((p4 → p2) ∨ p3) ∧ p5) ∧ (p3 ∧ p3)) ∨ (p5 ∨ p3)))) ∧ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50082121133335498184217785727 : (((False ∧ (((True ∨ (p2 ∧ p5)) → True) ∧ ((False → (((True → True) → False) ∨ (True → False))) → p2))) ∧ (p3 ∧ ((True ∨ p3) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37108624346167866521762028534 : (((((((((True ∨ (p2 → p4)) ∨ True) → p2) ∧ (p5 ∧ ((True → True) → p2))) → (((p5 → True) ∨ p3) ∧ True)) → p2) ∧ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810300678020744081386392685550 : (((p5 → ((p4 ∧ (p3 ∧ (True ∧ ((p3 ∧ p4) ∨ (p4 → (p4 ∨ p4)))))) ∨ (((True ∨ (((p1 ∧ p4) → p5) ∧ p3)) ∧ p4) ∨ p5))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666171396927758364663809711986 : ((((((p3 → (p1 ∨ ((p2 ∨ (p5 → ((p2 ∨ False) → p3))) → p3))) ∧ (p5 ∧ (p2 ∧ p5))) ∨ (p2 → p1)) ∧ (p4 → (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249048577872522612876312143115 : ((p4 ∨ p1) ∨ (((p3 ∧ (((p1 ∨ p1) ∧ p4) ∨ p3)) ∨ (p1 → ((p3 ∧ p3) ∨ (p1 ∧ ((((p3 ∧ True) ∧ p2) → p3) ∨ p3))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785507871471224628304019166200 : (((p4 ∨ ((True ∧ ((True ∨ (((p4 ∧ p4) → p2) → (False → ((p3 → (True ∧ p1)) ∨ (p1 → p2))))) → ((p2 → False) ∨ True))) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316905145101927879748145663178 : (p3 ∨ (p1 → (p5 → (False ∨ ((True ∨ p5) → (p2 → ((((p2 ∨ (p2 ∨ p2)) ∧ p5) → (p2 ∧ p1)) ∧ ((True → False) → (False ∧ p3))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  -- Conjunctions on the left can always be decomposed.
  let h18 := h5.left
  let h19 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- Implications on the right can always be decomposed.
  intro h30
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h31 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h33 := h30 h32
    -- False on the left can always be used.
    apply False.elim h33
  case inr h34 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h35 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h36 := h30 h35
    -- False on the left can always be used.
    apply False.elim h36
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h37 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h38 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h39 := h30 h38
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h42 := h30 h41
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225411362663431772099221609778 : (((p3 ∨ False) ∧ p1) ∨ ((True ∧ (False ∨ p3)) ∨ (False → (((True ∧ p1) → (((p4 ∧ True) → ((p5 ∧ False) ∧ (p2 ∨ p2))) → p2)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3984083121367551129947615127 : (p1 ∨ (((p1 ∧ ((p5 ∧ ((True ∧ p4) → (p5 ∨ p2))) ∧ (p5 ∨ p2))) ∨ True) ∨ ((p5 ∧ p4) ∨ ((False → (p5 → p2)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42022765699191108684012801221 : ((((False ∧ p3) ∨ (p3 ∨ ((True ∧ p4) ∧ (((False ∧ (((p1 ∧ p2) ∨ p1) ∧ (False ∨ (p4 → (p1 ∧ p1))))) ∧ p5) ∧ p4)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206709793345297469340364306423 : ((p3 → (((p2 ∧ p2) ∨ p4) ∧ p4)) ∨ (((True ∧ True) → (p1 ∧ (p5 → p2))) ∨ ((p3 → ((False ∨ p2) ∨ p3)) ∨ (p3 ∧ (p3 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



