variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206077986514174012530288396437 : ((p3 ∧ ((p3 ∨ p1) ∨ (p5 → p3))) ∨ ((p5 ∨ ((p2 → ((False ∧ False) ∧ (((p1 → p1) → False) ∧ True))) → (p5 ∨ True))) ∨ (p3 ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299358206295802751251491967392 : (False ∨ (((p4 ∧ p5) ∧ (p4 ∧ (True ∧ ((((p1 ∧ p4) ∨ (False → (((((p1 ∨ p5) ∧ p2) ∧ False) → p4) ∧ p3))) ∨ p1) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231533546853182620953722733579 : (((p4 → p4) ∨ True) → (p4 ∨ (((p2 → ((((p2 → True) ∧ p1) ∧ (p4 ∨ p5)) ∧ p3)) → (p3 → (p4 → p2))) ∨ (False → (False ∧ p3))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115963763445628917748940435599 : (((((p5 ∧ p5) ∧ p3) ∧ p3) → (((p3 ∨ p4) → p5) → ((p2 ∧ (((p1 → (p4 ∧ (False ∨ p2))) ∧ p3) ∧ p5)) ∨ p5))) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355554560608116052051693505141 : (p5 → (((((p3 ∧ True) ∨ p2) ∧ (((False → (p2 ∨ (p3 → p5))) ∨ p4) → (p2 → (p5 ∨ (p2 ∨ (p1 ∨ True)))))) → p1) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176894027366639313277403383429 : (((p2 ∧ False) ∨ (p1 ∨ ((((p3 → p5) → p2) → p3) ∨ (True ∨ True)))) ∧ (p1 ∨ (False → (((False ∨ p3) → p2) ∧ ((p2 ∧ p2) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352782304234912344450702166895 : (p4 → ((True ∨ p3) → ((True ∨ p1) → (((p5 ∧ ((p5 ∨ p2) ∨ p1)) ∧ (p4 → (False → ((p2 → (p1 → p1)) → p3)))) ∨ (True ∨ p2))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811488077211230887929046539730 : (((p5 → (p4 ∨ ((False → p4) → ((p1 ∧ True) ∧ ((False ∨ ((p4 ∧ (p3 ∨ (p3 ∨ (p2 → True)))) → ((p5 → p4) → True))) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323814431680026789130022951012 : (p5 ∨ ((((p4 ∨ (((True ∧ (p3 ∨ p3)) ∨ (p5 ∧ (p1 ∧ p5))) ∧ (p1 → False))) ∧ p1) ∧ p2) → (((p4 ∨ (p5 ∨ False)) ∨ p3) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h21 := h9 h20
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472183243788287628796732745730 : (((((p4 ∨ p1) ∧ (p4 ∨ ((p4 ∧ (False ∨ p4)) ∧ (p1 ∨ p1)))) ∨ (((p5 ∨ (p3 ∧ (True ∧ (p1 ∧ True)))) ∧ False) ∨ (False → p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303874367722013396920066399924 : (p1 ∨ ((((p2 ∨ (p2 ∨ (((True ∨ p3) ∧ p4) → ((p2 ∧ ((False ∧ p5) ∨ True)) ∨ p2)))) ∧ p2) ∧ (p4 ∨ ((True ∨ True) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41052687463271180939064269715 : (((((p2 ∨ True) ∧ ((p4 ∨ (True ∧ True)) → (((p4 ∨ p2) ∨ ((p5 ∧ ((p4 → p3) → False)) ∧ p5)) ∨ True))) → (p4 ∨ p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181642556802191788187401757910 : ((p3 → (((((p5 ∧ p4) ∨ p2) ∨ (False ∨ False)) → p2) ∨ (p5 ∨ False))) → ((((p3 → p1) ∨ p3) ∨ p4) ∨ ((p1 → p5) → (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199695096360718116986601928004 : (((True ∧ (False → ((p5 ∨ p1) → p5))) → p1) → ((p4 ∧ (p5 → ((p4 ∨ p3) → (p2 ∧ ((p5 ∨ p4) ∧ (p3 ∧ p1)))))) ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (False → ((p5 ∨ p1) → p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255817162444174475761067771697 : ((True ∨ False) → ((False ∨ ((True → False) ∨ False)) → (True ∧ (False ∧ (((False → False) ∧ ((True ∧ (((False ∨ p4) ∨ True) → p2)) → False)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h8 := h5 h7
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57009231662469811642498338380 : (((False → (False ∧ p4)) ∧ (p2 ∧ (((((((p2 ∧ False) ∨ (p5 → (p5 → p4))) → False) ∨ False) ∨ ((p5 ∨ p1) ∨ p2)) ∧ p3) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41696936947180793645421630104 : ((((((p3 ∧ (True → p4)) → p2) → p1) → ((((True → ((True ∨ p1) ∧ p2)) ∧ p4) ∨ ((True ∧ p1) → (True ∨ p2))) ∧ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59059310208500367734443247157 : (((p4 ∧ p5) ∨ (((False ∨ p2) ∨ (((((False ∧ (((p5 ∨ p5) → True) → p3)) ∨ (p1 ∧ p4)) ∨ p1) → p1) ∧ p3)) → (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3389653699345865409681516715 : ((p2 → p2) → ((True → ((False ∧ p4) ∧ p4)) ∨ ((True → p4) → (p1 → (p2 ∨ (((p1 ∧ False) ∧ ((p4 ∧ p1) ∨ True)) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789981880491094019423220445283 : (((p5 ∨ ((False → False) ∧ (((False → False) ∧ p3) → ((((True ∧ True) ∨ p3) → (p2 ∨ (p5 → ((p3 ∧ (p4 ∧ False)) ∨ p4)))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622738901836767709039186928291 : ((((p4 ∧ (True ∧ (p3 → ((p5 → (((p4 ∨ p2) ∨ p3) ∧ (p1 → ((p3 → (False ∨ p4)) ∧ p2)))) ∧ ((False → p2) → p3))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_190925680536114553721965516198 : ((((p1 ∧ (p1 ∧ p3)) ∨ p3) ∧ ((p2 ∧ False) ∧ p4)) ∨ (((p3 ∧ False) ∧ p1) → ((((p1 ∨ False) → p5) ∨ p3) → (False ∧ (p4 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h22
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133982927317571185520555564501 : ((((((True → (True ∧ (p2 → (p4 → ((p3 ∨ (p2 ∨ p4)) ∨ p1))))) → ((False → p3) ∧ True)) → p4) ∧ p3) ∨ p3) ∨ ((p5 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53218390698848687765941026000 : (((((p5 → (p4 ∨ True)) → (True ∧ p5)) → ((p2 ∨ p1) ∨ p4)) ∨ ((True ∧ p5) ∨ (p2 ∧ (((p1 ∨ True) ∨ (False ∨ True)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65769621271742912138038569264 : ((p4 ∨ (((((False → False) ∨ p4) → (((p5 ∧ p4) → p4) ∨ True)) → ((True → p4) → p1)) ∨ (p5 → ((p4 → p4) ∧ (p5 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245981299950304990003624447630 : ((p4 ∧ True) ∨ (((p1 → p1) → p5) → (((False ∧ ((((False ∨ False) → ((p1 → (False ∨ False)) ∧ p4)) ∧ p3) ∨ False)) ∨ (p3 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193207598526334351482355686983 : (((p1 ∨ (False → (p2 → p3))) → ((p1 → True) ∧ False)) → (((((False ∧ (p2 ∧ p3)) ∧ p5) ∨ p2) ∧ p1) ∨ (p5 ∧ ((p1 → True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (False → (p2 → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677578402651709755517672260280 : (((((p5 → ((p5 → ((p5 ∨ (p5 ∨ (p3 ∧ p4))) ∨ ((p2 ∧ p1) → (p3 ∧ False)))) → False)) ∨ p2) ∨ ((p3 → (p1 → p1)) ∨ p5)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141196233500942494539306628583 : ((((False → p5) ∧ ((p3 → p4) ∨ p2)) ∨ ((p2 → (False ∧ (((p3 ∧ (p4 ∧ p3)) ∧ (p4 ∧ p1)) ∧ p2))) ∧ p3)) → ((p2 ∧ p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42760874899178322187190568377 : (((True → (p5 → ((False ∨ (((p5 → (p1 ∨ (p2 ∨ p4))) → ((False → p4) → p5)) → ((p3 → p4) ∨ (p4 ∧ p3)))) → p3))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115117993604627148682249717429 : ((((((p2 → ((p4 → False) → p5)) → True) ∧ p2) ∨ (True ∧ True)) → (((((True ∨ p2) ∧ (p3 ∨ False)) ∨ p3) ∨ p5) ∨ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157887686557560901127602909328 : (((p3 ∧ ((p1 → (p3 ∨ (p3 ∧ (p3 ∨ p5)))) ∧ p5)) ∨ ((True ∧ True) ∨ ((p3 ∧ p2) → p3))) ∨ ((True ∧ True) → ((p1 ∧ p1) ∧ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47674011944492883505219115991 : (((((p3 ∨ (True ∧ p5)) ∨ (((p4 → True) ∧ True) ∧ (p5 → (p1 → (((p5 ∧ p2) → p5) ∨ (p1 ∧ p2)))))) ∧ p2) → (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351662687642746269221465869319 : (p4 → ((((False ∧ (True ∨ (p1 ∨ False))) ∧ (p1 ∨ ((True ∨ (False ∨ p5)) ∨ True))) → p5) → (((p5 → (p1 ∧ (p5 ∧ p5))) ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184991438853458144484118862390 : (((p1 ∧ True) ∧ (((p4 ∧ ((p2 ∨ False) ∧ p4)) ∨ p1) ∧ p5)) ∨ (((((p3 ∨ (p2 ∧ False)) → ((False ∨ p3) ∧ False)) ∨ True) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231630724295526263310385197927 : (((False ∧ False) → p1) → (p2 ∨ (((p4 ∨ (True → (p4 ∨ ((p5 ∨ (p5 ∨ True)) ∧ (((False → False) ∧ p5) ∧ p1))))) ∨ True) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167355438052927661390813650353 : ((((p5 → ((p1 → (True ∧ p5)) → (p2 ∨ p5))) ∨ (((p2 ∨ p4) → p2) ∧ p4)) → p1) → ((((p1 ∨ p3) → (p3 ∧ False)) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 → ((p1 → (True ∧ p5)) → (p2 ∨ p5))) ∨ (((p2 ∨ p4) → p2) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323203118987375081325985361074 : (p5 ∨ (((False ∧ (((p5 ∧ p4) ∨ ((p2 ∧ p5) ∧ p2)) ∧ (False → (((p4 ∨ p4) → p2) ∧ (False ∧ p2))))) ∨ (True ∨ p2)) ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601936518912271522799846326846 : ((((p4 ∧ (False ∨ ((((p2 ∧ False) ∨ p2) → False) ∧ (((p1 → (True ∧ ((False ∧ (p2 → (p1 ∧ p1))) → True))) ∨ p2) → p4)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54754394641471020650797076756 : ((((p5 ∧ p1) ∨ (((p4 ∧ p1) → p5) ∧ p4)) → ((False ∧ p5) ∨ ((p1 ∨ ((True ∨ (p5 → (p4 ∧ p1))) → (p1 ∧ p4))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147840022538411843345223585177 : (((p3 ∨ (((p5 ∧ p5) ∧ (p3 ∨ False)) → (p4 ∨ (((False → (False ∧ p4)) → (True → True)) → True)))) → p1) ∨ ((False → p2) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117363477305086188539205249402 : ((False ∧ (p2 ∨ (False ∨ (((p3 ∨ (p5 → p2)) ∧ p2) ∧ ((p4 ∧ (False ∧ ((p1 ∨ False) ∧ (p2 ∧ (False → False))))) ∧ False))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44503081756146735928896098472 : ((((p2 ∨ (p3 ∨ (p4 ∧ ((p1 ∨ p1) → (False → True))))) ∧ ((False ∧ ((False ∨ p2) → p3)) → (((p1 → False) ∨ p4) ∨ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180425411399045303053721864629 : ((((True → (p1 → ((p5 → p5) ∨ (False ∧ True)))) ∨ p1) → (p2 ∨ p1)) → (p5 ∨ (((((p2 ∨ (False ∧ p5)) ∧ True) → p5) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259379155604022646229714926701 : ((False → p3) → (((False → p1) → ((((((p3 ∨ p1) ∨ p1) ∨ False) → ((True → p4) ∨ (True ∧ p3))) ∨ p4) ∧ ((False ∧ p5) ∧ p5))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111501528003108848520578533869 : (((p4 → (((p4 ∨ ((((p3 → (p5 → p2)) ∧ p2) → ((False ∨ False) → p5)) → (p4 → (False ∧ p2)))) ∧ p2) ∨ False)) ∧ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259030388558837892595014495951 : ((True → p4) → ((((p2 ∧ p5) ∨ (((p4 ∨ False) → p1) ∨ p2)) ∨ True) ∨ (((True → p2) ∨ p2) → (((p1 ∨ p2) ∨ p1) ∧ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313085219017518372444926382618 : (p3 ∨ (((((p1 ∨ (True → p4)) → (False ∨ True)) ∧ (((p1 → (((p3 ∨ (False ∧ p3)) ∨ p4) → p3)) ∧ p4) ∨ False)) ∨ (False → True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191731155514025473456445974079 : ((False ∨ (((p2 ∨ (p1 ∧ True)) ∨ (p2 ∨ p1)) ∨ p5)) ∨ ((False ∨ (True ∧ ((p3 ∨ p1) ∨ (p4 → (True ∧ (p3 ∨ (p4 ∨ p3))))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120096038394184670791444682499 : ((((p4 ∨ (p5 ∨ (p2 ∨ p3))) ∧ ((p4 → (p5 ∧ False)) ∧ (True → (((False → p5) ∨ p5) ∧ ((p5 → p2) ∨ p4))))) ∧ p5) → (p4 → False)) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h6.left
        let h23 := h6.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h25 := h22 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h6.left
        let h29 := h6.right
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h30 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h31 := h28 h30
        -- We need to get the right conjuct of h31 based on <expert-advice>.
        let h32 := h31.right
        -- False on the left can always be used.
        apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256625181499741224214892986904 : ((p1 ∨ True) → (p5 ∨ ((p5 ∧ p5) ∨ ((p1 → False) → ((p3 ∧ (False ∧ (True ∧ p5))) ∨ (p2 → (p2 ∨ (p2 → (p3 → (p5 ∨ p2)))))))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759728727051788192699265139756 : (((p2 ∧ ((((p4 → p2) ∧ p5) ∧ (((False → (p1 → True)) ∧ p4) ∧ p1)) → (((((p3 → p3) → False) ∧ p1) ∨ True) ∧ (p4 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319363484335479641322952457984 : (p4 ∨ ((((p5 → (p1 → True)) ∧ (((p2 ∧ p4) → (p5 ∧ p2)) ∧ p5)) → False) ∨ (p4 → (p5 ∨ ((p4 ∧ ((p5 ∧ False) ∧ p2)) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181070590304599424895573793352 : (((p1 ∨ False) → (True → (p4 ∧ (((p4 → (p2 ∧ True)) → p4) ∧ p2)))) → (p1 → ((p5 → False) ∨ ((True → p2) → (p3 ∨ (False ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173334219780111850831039339457 : ((p2 → ((p3 ∨ p4) ∨ (p5 ∨ (((p1 ∧ (p5 ∧ (p4 → p2))) → p1) ∧ p1)))) ∨ (False → (p1 → ((False → (p1 ∧ p4)) → (p1 → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_903182008658222037019478922355 : ((((p4 ∧ (((p2 → (((True ∧ ((p3 → (False → True)) → p3)) ∧ (p4 ∨ p4)) ∧ True)) ∨ True) → False)) ∧ (p1 ∨ (True ∧ (p5 ∨ p3)))) → p3) ∧ True) := by
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
    have h7 : ((p2 → (((True ∧ ((p3 → (False → True)) → p3)) ∧ (p4 ∨ p4)) ∧ True)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
      have h13 : ((p2 → (((True ∧ ((p3 → (False → True)) → p3)) ∧ (p4 ∨ p4)) ∧ True)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_554687475016106310958895232081 : (((p2 ∨ ((p2 → p1) → (((p4 ∧ True) → False) → ((False ∨ True) ∧ ((p3 ∨ True) → (((((p1 → p2) → p5) ∧ p2) ∨ True) ∨ p3)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
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
theorem thm_5_vars_620421528088887422685376608999 : (((((p5 ∨ p1) ∨ ((p3 ∨ ((((p4 ∧ ((False ∧ False) ∧ False)) → (((p4 ∧ p5) → p5) ∧ False)) → p5) ∧ (p4 → p5))) ∨ True)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780303009044063717546014545627 : (((p2 ∨ ((((p2 ∧ p2) → (((p1 ∧ (p4 ∧ p1)) → (False ∧ (p4 ∨ (False ∧ p4)))) ∧ p5)) ∧ False) ∨ (False ∨ ((p1 ∧ p5) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200855696319705889532638707972 : ((True ∨ (True ∧ (False → ((p2 ∧ p2) ∧ p3)))) → ((((p2 ∧ p5) ∧ (p1 → p1)) → (((p4 ∧ (p5 ∧ (True ∨ True))) ∨ p3) → p2)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780359990127537276348467709224 : (((p2 ∨ ((p5 ∨ (((p1 ∨ p2) ∨ ((((True ∧ True) → p3) ∨ p5) ∨ p4)) ∧ (False → (p4 ∨ True)))) → ((p1 ∧ p4) ∨ (p1 → p1)))) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259479407772325844363757327064 : ((False → p4) → (p5 ∨ (((p2 ∨ p5) ∨ (False ∨ True)) → ((p3 ∧ ((p2 ∨ (p3 ∨ (p2 → ((True → p2) ∧ p3)))) → p1)) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148280392177655746079459569322 : ((((p3 ∨ ((p4 ∨ ((p3 ∧ p4) ∨ (p1 ∨ (p1 → False)))) ∧ (p1 → False))) ∨ p5) → ((p5 ∨ p4) → p2)) ∨ (((False → p1) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67514883381853580230211157141 : ((p1 → (((p3 ∨ p1) ∨ (p4 ∨ (p2 → False))) ∧ ((p2 → p4) ∨ (((p3 ∨ True) → p4) ∨ (p5 ∨ (False → ((p2 ∧ p2) ∨ p3))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225553125468773234285843505319 : (((True → p4) ∧ p3) ∨ (((((((True → ((True → ((p5 ∧ (p3 → p3)) ∨ p4)) ∨ False)) → False) ∨ (False ∧ False)) ∧ False) ∧ p4) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230483826667707887601061346290 : (((True → True) ∧ p2) → ((((p5 ∧ p1) → ((((p2 → p1) ∨ (((p3 ∧ p1) ∨ p2) → p2)) → p4) ∧ False)) ∨ ((p2 ∧ True) → p2)) ∨ True)) := by
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
theorem thm_5_vars_737076922041607864475989726895 : ((((p3 → p2) ∧ (p3 ∨ ((p2 ∧ (p3 → (p3 → True))) ∧ ((p4 → False) ∧ ((True → (((p2 ∨ p5) → p1) ∨ p4)) ∧ (p4 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695478747092001194074269808676 : (((((((p2 → ((p5 ∧ p3) ∧ p3)) ∨ True) → (p4 ∨ False)) → (p4 ∧ False)) → (((True → (p3 ∨ p5)) ∨ True) ∨ ((p2 ∧ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602745815741022373937540434033 : ((((False ∨ (p2 ∧ (p1 ∨ (p5 ∧ (p5 ∧ ((p1 ∧ (p1 ∧ (((p4 ∧ (True → p5)) ∨ p5) → (p2 ∨ (p2 ∨ False))))) ∨ p3)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86587736691913539476532932187 : (((((p1 ∧ (p2 ∧ p4)) → (p3 → True)) → False) ∧ (((p5 ∧ p1) ∧ ((p1 → p2) ∧ p1)) → (True → ((False ∨ p5) ∧ (p3 ∨ p3))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ (p2 ∧ p4)) → (p3 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52572895714486705264809084009 : (((((p1 ∨ p4) ∨ ((p4 → (False ∨ (p5 → p1))) ∨ p2)) ∨ (True → p5)) ∨ ((p2 ∨ (True ∧ True)) → ((True ∨ True) ∧ (p3 ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157082864229439970801142271773 : (((p4 ∨ (((p1 ∧ True) ∨ ((True ∧ p5) ∨ ((p5 → (p3 ∧ (p5 ∨ p4))) ∨ p4))) ∨ p2)) ∨ p2) ∨ (((p5 ∧ True) ∧ (p4 ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595886121063986543102476726100 : (((((((p2 ∧ (False → p1)) ∨ (p1 ∨ (True ∧ p3))) → p1) ∨ ((p3 ∨ True) ∧ (((p1 ∧ p4) ∧ (p5 ∨ p3)) ∨ (p2 ∨ p2)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112065434062568328195076090946 : ((((p4 ∨ p4) ∧ ((((p4 ∨ ((((p1 ∨ (False → p5)) ∧ (p2 → p5)) ∧ p4) → p5)) → p3) ∧ p5) ∨ (p5 → p5))) ∨ p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45003654541011466030056410567 : ((((p2 ∧ True) ∨ ((False → p4) ∧ (((True ∧ ((((p2 ∧ p3) ∨ ((False ∧ False) ∨ True)) → (p3 ∧ p4)) ∨ p3)) ∧ p5) → p2))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191578356397381964595602983518 : ((p2 ∧ (((True ∧ p2) ∧ p1) ∧ ((p2 → p4) → p1))) ∨ (((False ∨ p2) → ((p5 ∨ p3) ∧ True)) → (True ∨ (((p4 ∨ p4) ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151607634783688689666315064997 : (((True ∧ ((p5 ∧ (p1 → (p5 ∨ (p4 ∨ True)))) ∨ ((p4 → (p2 ∧ (p3 → True))) → p2))) → (p3 → p3)) → (((p4 ∨ True) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304985634890354094936616509365 : (p1 ∨ (((p1 ∧ (((p2 ∨ (((True ∨ False) ∧ ((False ∧ p5) → p5)) ∧ (p2 → True))) ∧ p5) ∧ (p3 → False))) ∨ False) ∨ (False → (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115802669831902543296057473187 : (((((False → p4) ∧ p1) → p3) ∧ ((p2 ∧ p3) ∨ ((p3 ∨ ((p3 ∧ (p1 ∧ p4)) ∧ ((p4 → True) ∧ p3))) ∧ (p5 → False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705132745414497401177522776829 : (((((((True ∧ (p1 ∧ p1)) ∧ p3) ∨ p2) ∧ False) ∧ (p3 → ((((p1 ∧ (False ∧ p1)) → (p2 → (p4 ∨ p1))) → p5) ∨ (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40446375926029518100114741268 : ((((((p1 ∧ p1) → (p2 ∧ (p1 → False))) ∧ ((p2 ∨ (((False ∨ ((p3 ∨ p2) ∧ p4)) ∧ (p3 ∨ p4)) ∧ False)) ∧ p5)) ∨ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47028785513606541439831497857 : ((((p3 → ((p1 ∨ p3) ∧ ((p5 ∨ ((p1 → (((p3 ∧ p2) → ((p1 → p4) → p3)) ∧ p4)) ∨ p5)) ∧ p2))) → False) ∨ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350453474157253587961025508333 : (p4 → ((((((p3 ∧ (False → p5)) ∨ (p3 ∧ (p5 ∧ p1))) ∧ (((p2 ∨ p4) → p2) ∧ (p1 ∧ False))) ∨ ((p3 ∧ p1) ∨ p4)) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p3 ∧ (False → p5)) ∨ (p3 ∧ (p5 ∧ p1))) ∧ (((p2 ∨ p4) → p2) ∧ (p1 ∧ False))) ∨ ((p3 ∧ p1) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2119973744744432736788771557 : ((((((False → False) ∨ (p3 ∨ p3)) → p4) ∨ (p2 ∨ (p4 → p4))) → ((p1 ∨ p2) ∧ p1)) → (((True ∧ (True ∨ p2)) → p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → False) ∨ (p3 ∨ p3)) → p4) ∨ (p2 ∨ (p4 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681388810489820981035849439575 : ((((p2 ∨ ((p3 ∧ ((True → p3) ∧ ((p4 → (((p5 ∧ p4) ∨ p4) → (p3 → p5))) ∧ p2))) → False)) → (p1 ∨ (p5 ∨ (p1 ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_116544237930218503607187877745 : (((False ∨ p3) ∧ ((p2 ∧ ((p5 → False) → (True ∧ (p3 ∨ p3)))) ∧ ((((((True → p1) ∨ p1) ∨ True) ∨ p3) → p3) ∨ p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353868116872513734956024692272 : (p4 → (p1 → ((True ∧ p4) ∧ ((((((((p4 → False) ∧ (False ∧ p5)) → True) ∨ (p1 → p1)) ∨ (p2 ∧ p3)) ∨ False) → (False ∧ False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130073031284443669602942395403 : ((((((p3 ∧ True) ∧ (((False ∧ False) ∨ ((True ∨ (p2 → (p2 → p4))) → True)) → True)) → p4) ∧ p3) ∨ (p1 ∨ True)) ∧ ((p1 ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_732991147188881327369787521721 : ((((p2 ∧ p4) ∧ ((p4 ∧ (((p2 → True) → ((True ∨ ((p4 → p2) ∨ True)) ∧ (False → (p5 ∨ p3)))) → ((p1 → False) ∧ True))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117946029358334090699284080750 : ((p5 ∧ (p4 ∧ (False ∨ ((((((False ∧ p3) ∧ (p5 ∧ (p4 ∧ False))) ∧ (p4 ∧ p1)) → p5) ∨ p5) → ((p2 ∧ True) ∨ p1))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205154622996342429701640607807 : (((p1 ∧ (False ∧ p5)) ∧ (p4 ∨ p1)) ∨ (p3 → (((False ∨ True) ∧ (p2 ∨ ((((False ∧ False) ∧ p1) ∧ (p2 ∨ (False → p2))) → p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206358737056997605989149880243 : ((p2 ∨ ((True → p1) ∨ (False ∧ p3))) ∨ ((p5 → p1) ∨ (p3 → (((p3 → False) ∧ (True ∧ p4)) ∨ (False → (p4 ∧ ((p4 ∨ p1) → p2))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111431686839420777124327536113 : (((p4 ∨ (p2 ∧ (((p2 ∧ p1) ∨ (p2 ∨ False)) ∧ (p4 ∧ (p4 ∧ (p4 → ((p2 ∧ p1) ∧ ((p1 ∧ p4) → p1)))))))) ∧ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302697030107393702529794266911 : (False ∨ (p3 ∨ (((p2 → (p2 ∧ p4)) ∧ (False ∨ ((((p3 → True) → ((p3 ∧ False) → p5)) ∧ p2) ∧ False))) ∨ (p1 → (False → (p3 ∧ p3)))))) := by
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
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338517227267061875497915721928 : (p1 → (((False ∨ p4) ∨ p2) ∨ ((p1 → ((((((p1 → True) ∨ p3) ∧ p3) → False) ∧ p5) ∨ ((p4 ∨ p4) ∧ p5))) ∨ ((False ∧ p3) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356436216533987459730144705586 : (p5 → ((((((p4 ∨ (False ∧ p5)) ∨ True) ∧ (p5 ∨ p1)) → p4) → False) ∨ ((True ∧ (p5 → (((p1 ∧ (True ∨ p3)) → p5) → p5))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777413799488026352332593120922 : (((p1 ∨ ((((False ∧ (((p1 ∧ (p1 → p1)) ∨ p1) ∧ p5)) ∨ (p1 → (p1 ∨ False))) ∧ False) ∨ (((True ∨ True) ∨ p5) ∧ (p1 → p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171469646272603441612118381211 : (((p2 ∨ (((p5 ∨ (p2 ∧ (p4 → ((p4 ∧ p2) → True)))) ∧ p1) ∨ p1)) ∧ p4) ∨ ((True ∨ False) ∨ (p3 ∧ (((p1 ∧ p5) ∧ p4) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340986968672271162091390748724 : (p2 → (((p3 ∧ p3) → (((((p1 ∧ (p5 ∨ (p1 ∨ p3))) ∨ True) ∧ False) ∨ ((p5 ∨ p3) → (p1 → p5))) ∨ ((p5 ∧ p2) → p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114907497347272260734007523847 : ((((((False → p5) ∨ True) → ((p5 → ((False ∧ False) → p1)) ∧ False)) ∧ p3) → (((((p5 ∨ False) ∧ False) → p1) → p2) ∨ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



