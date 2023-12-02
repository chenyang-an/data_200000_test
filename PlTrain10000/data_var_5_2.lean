variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740119933844578272028615319573 : ((((False ∨ p3) ∨ ((p2 → (p4 → ((p3 ∨ (((True ∧ (p5 ∨ (((p4 ∨ True) → True) → False))) → False) ∨ (p3 ∧ p3))) → p3))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_737627880524488940844605515425 : ((((p5 → p2) ∧ (p3 ∨ ((p1 ∨ (((False → (p4 ∨ p3)) ∧ (p1 ∨ ((p4 ∨ True) ∨ p5))) ∨ (False → (p3 → False)))) → (True → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942361053886751448103061661740 : ((((((p5 → True) → p3) ∨ p1) ∧ ((True → ((p2 ∧ p1) ∨ (True ∨ (p2 → (p3 ∨ (p1 ∧ p1)))))) → ((False ∧ (True ∧ p5)) ∨ p4))) → p4) ∧ True) := by
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
    have h5 : (True → ((p2 ∧ p1) ∨ (True ∨ (p2 → (p3 ∨ (p1 ∧ p1)))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (True → ((p2 ∧ p1) ∨ (True ∨ (p2 → (p3 ∨ (p1 ∧ p1)))))) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138055582992191255363333966639 : ((True → (False ∧ ((p4 ∧ p1) ∨ ((p4 → p4) ∧ (p4 ∨ ((True → (p4 → (p1 → False))) → ((p1 ∧ p4) ∧ p5))))))) ∨ (False → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697337589879236713761804840425 : (((((p2 → p3) ∨ ((p2 → True) ∧ (p5 ∧ (p4 ∨ (p1 → p1))))) ∧ ((((p2 ∨ (p4 ∧ (p1 → False))) ∧ p2) → (p4 → p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318604403728292616269439757233 : (p4 ∨ (((((True ∧ p5) ∧ p3) ∨ (p5 ∧ (p3 ∨ p3))) → ((p3 ∧ p3) → ((p1 ∧ (p4 ∨ True)) ∧ (p4 ∨ (p3 ∨ p1))))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215262501632763778568576058244 : ((False ∧ (False ∨ (True ∧ p3))) ∨ (((((p5 ∧ p5) ∧ True) ∨ ((True ∧ True) ∧ p3)) ∧ p5) ∨ (p5 → ((p2 ∧ p2) → (p4 ∨ (p1 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748654625575929068123564230129 : ((((p3 → p3) → ((((p4 ∧ (p3 ∧ (p5 ∧ ((False ∨ ((p4 → p2) ∨ ((p4 ∧ p1) → (p3 ∧ p1)))) ∨ p1)))) ∧ p4) ∨ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177761966735735244452440439995 : ((((True ∨ False) → ((p2 → ((True ∧ False) → p5)) → (p2 → p2))) ∧ False) ∨ (((((p1 → (False ∨ p5)) ∨ (p2 ∧ p3)) → p3) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68334420430649862376656518876 : ((p3 → (((p4 → True) ∨ (False ∨ (False ∧ (((p2 ∨ (p3 ∨ False)) ∨ p4) → p2)))) → ((True → ((p3 ∧ (p1 → p5)) ∧ p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213751376088192922316290133453 : ((((p3 → True) → p4) ∨ p2) ∨ (True → (True → ((((False ∨ (p1 ∧ p5)) → True) → ((p5 ∨ p4) ∧ p3)) ∨ ((False ∨ p2) ∨ (p5 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245162724046538319490205167750 : ((p2 ∧ False) ∨ (((p5 ∧ p2) → ((p4 ∨ p3) ∨ (((p2 → p2) ∧ p3) → (((p5 → p4) ∧ ((p4 ∧ True) → (False ∨ True))) ∨ True)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670917202291218257974330024839 : ((((p4 ∧ (((((p2 ∨ ((p5 ∧ (p5 ∧ p1)) ∨ p4)) ∧ (p2 → ((p5 ∨ True) ∨ p5))) ∧ p2) ∧ p4) ∧ True)) ∨ ((False → p5) → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_569593396363081109745353019 : ((((((((p5 ∨ False) ∨ p4) ∨ p2) → (False ∧ ((((p1 ∨ p5) ∨ p5) ∨ p2) → ((p2 ∧ p1) ∨ p2)))) ∨ p4) ∨ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67680983532639899659556148242 : ((p1 → (p1 → ((((p3 → p1) → (p1 → ((p4 → (p3 ∧ p5)) ∨ (p2 → (p4 ∨ p4))))) ∧ p2) ∧ (((p2 ∧ False) → p4) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208956431354382001339607176752 : ((True ∨ (((False ∧ False) → p5) → False)) → (((p5 ∨ (p3 ∨ ((False → p3) ∨ p1))) ∨ True) → (((False ∧ p3) → (p2 ∧ p2)) ∧ (False ∨ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
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
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161527558525524930391412853280 : ((p5 ∧ (((False ∨ True) ∨ (((((False ∧ True) ∨ ((False → p3) → p4)) ∨ p2) → p5) ∧ p2)) ∧ p4)) → (((p2 ∧ p1) ∧ False) ∨ (p2 ∨ p4))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134860624912298053194868539620 : (((True → (p5 ∨ ((p2 → (p1 → ((((p2 ∧ p1) ∨ p4) ∨ (p3 ∨ (p1 ∧ p2))) → p2))) ∨ (p2 ∧ p4)))) → p1) ∨ ((p3 ∧ False) → p4)) := by
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
theorem thm_5_vars_141284538404999705042731752484 : ((((False ∨ p1) ∧ (p4 → p1)) ∧ (True → (((p3 ∧ p2) → (((False ∨ p3) ∨ p5) → p2)) → ((p2 ∧ False) ∧ p2)))) → (False ∨ (p4 ∨ p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 ∧ p2) → (((False ∨ p3) ∨ p5) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h11.left
          let h17 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h11.left
        let h20 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h20
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h21 := h9 h10
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126640994518118810700112999531 : ((p3 ∧ (False ∨ (((p3 ∨ (((p4 → ((p5 → (True → False)) → ((p4 ∨ p4) ∧ p2))) → p4) ∨ p1)) → p1) ∧ (p4 ∨ p5)))) → (p1 ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (p3 ∨ (((p4 → ((p5 → (True → False)) → ((p4 ∨ p4) ∧ p2))) → p4) ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∨ (((p4 → ((p5 → (True → False)) → ((p4 ∨ p4) ∧ p2))) → p4) ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113681450156932570084956128904 : ((((p3 → ((p5 ∧ p5) ∨ ((((p4 ∨ p4) ∧ p3) → ((p5 ∨ ((p4 → True) → p4)) → p2)) → p1))) ∨ p3) → (p5 → p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117071022252861979177273325582 : (((True → p2) → ((p5 ∨ ((False → (p1 ∧ (((p4 ∧ p3) ∧ p5) → p5))) ∧ (p1 ∧ ((True ∨ (p2 ∧ False)) ∧ p3)))) ∧ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3177669927433799748896420823 : ((True ∧ p4) ∨ ((p5 → p2) ∨ ((p4 ∨ (p3 → p2)) → (((p3 → ((True → p5) → p5)) ∨ True) → (p1 → (p3 ∨ (False → p4))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111800792888819593359741184997 : ((((((False ∨ (False → p4)) ∧ (((p4 ∨ (p1 ∧ (False ∨ p4))) ∧ ((p4 → p2) → p1)) → False)) ∨ p3) → (p5 → p3)) ∨ p5) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299270590885601288481603673309 : (False ∨ (((p1 ∧ (False ∧ (p1 ∧ (p1 ∨ (((True → False) ∨ p3) ∨ (p4 → (p4 ∧ p3))))))) ∨ ((p3 → ((p4 ∧ p4) → True)) ∨ p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481378590863558658024279618814 : ((((p4 ∧ (p2 ∨ (((False ∧ p4) ∨ p2) ∨ True))) ∨ (p2 ∨ (((p5 → ((p2 → (p4 ∨ True)) ∨ False)) ∨ p3) → ((True → p3) ∨ True)))) ∧ True) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134140739689252738257430187508 : ((((p4 → (((False ∨ p2) → ((p5 ∨ (((p2 ∧ p3) ∨ (p2 → p4)) ∧ p3)) ∧ p1)) ∨ p5)) → (p2 ∨ p2)) ∨ True) ∨ (p3 ∧ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151222654262600385389436628242 : (((((True ∧ p5) ∧ p5) ∨ (((p3 ∨ (True ∨ p1)) → p2) ∨ ((p2 ∧ ((False → False) → False)) ∧ False))) → p5) → ((p2 ∨ (p3 ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33492900138832848560886289999 : ((p4 ∨ ((True → (p3 ∧ True)) → (((False → (True → p2)) ∧ ((((p4 ∨ p1) → p1) ∨ (p1 → (True ∧ False))) ∨ (p4 → True))) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2298409591063071069648087256 : ((p4 → ((True → (False ∧ ((p3 → False) → (p3 ∧ (True ∨ p3))))) ∨ False)) ∨ (p1 → (p1 ∨ ((p2 → p3) ∨ (p2 ∧ (False ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888489904148398825077626570217 : ((((((p1 → (p4 ∨ True)) → (True → (p1 ∧ (True → ((False ∨ p5) ∧ p1))))) ∨ ((True ∨ p3) ∨ ((p1 → True) ∨ p3))) → (p4 ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → (p4 ∨ True)) → (True → (p1 ∧ (True → ((False ∨ p5) ∧ p1))))) ∨ ((True ∨ p3) ∨ ((p1 → True) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_42918203466382328737412098409 : (((p3 → (p5 → (((p1 ∨ ((p5 ∨ (True → p2)) → ((True → p1) ∧ (True ∧ p4)))) ∧ ((p4 ∨ p1) ∨ (False → p1))) ∧ p2))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786667473389496674028613490987 : (((p4 ∨ ((p1 ∧ ((p2 ∨ False) ∨ (p4 → True))) ∧ (((False ∧ ((((p4 ∨ ((p4 ∨ True) → p4)) ∧ p1) ∧ p3) ∧ p4)) ∧ True) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341763203805569901668338816668 : (p2 → ((p5 ∨ ((p1 → (((p2 → p4) → False) → p4)) → (((p2 → False) ∨ ((p4 ∧ (p2 → p2)) ∨ (True → p5))) ∨ p2))) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171946791056546012455832623048 : (((((p2 → ((p2 ∨ True) → False)) → (True ∧ p5)) → (p2 → False)) ∧ (p1 → False)) ∨ ((p5 ∧ False) ∨ (p1 → (((p5 ∧ False) → False) ∨ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715295665949961562481934096899 : ((((p3 → ((p4 ∧ p4) ∧ (True ∧ p5))) → (((((p2 ∧ (p1 → (p4 ∧ p5))) → p1) ∨ (p4 → (p2 ∧ True))) ∨ (True → p3)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252156398243240994550823055321 : ((p4 → p3) ∨ (((p1 ∧ ((True ∧ True) ∧ False)) ∧ (p5 → (p5 → (p1 ∧ (p3 ∧ (((True ∧ p1) ∧ (False ∧ p2)) ∨ p3)))))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224998365754359740554042783865 : (((True ∧ p3) ∧ p5) ∨ ((p1 ∨ (p4 ∨ ((True → False) → ((p4 ∨ p1) → p5)))) ∧ ((False ∧ ((p3 ∨ p4) ∨ (False ∨ p4))) → (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251659098470835647101738928756 : ((p3 → p2) ∨ ((((p1 ∧ True) ∨ (((p5 ∨ p3) ∧ (p2 ∨ ((False ∨ p3) → p4))) ∧ (p5 ∨ (p2 → p4)))) → (p4 ∧ (p2 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661812566128040740617924104546 : (((((p4 → ((p4 ∧ (True ∧ ((p5 → (p3 ∨ p2)) ∧ (p3 → True)))) ∨ (p2 ∧ True))) ∨ ((p2 ∧ p4) ∧ (p2 ∨ p3))) → (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337760837475286846362032162552 : (p1 → ((((((((p4 ∨ p4) → p3) → p4) ∨ p4) ∧ p4) → ((True → p5) ∨ p2)) → p4) ∨ (p5 ∨ ((((p5 ∨ p3) → p5) → p2) → p1)))) := by
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
theorem thm_5_vars_144006455702631540760638732561 : (((p2 ∧ (p1 ∧ ((False ∨ (p2 → (p4 ∧ (((p1 ∧ p3) ∧ p1) → p1)))) → (p2 → (p1 ∧ False))))) ∨ True) ∧ ((p1 → (p5 ∨ p1)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48697074787595483342879182005 : ((((((False → p3) → (p5 ∧ p1)) ∧ p3) ∧ (p4 ∧ (p2 → ((((p5 → p3) ∨ (True → p2)) ∨ p2) → p5)))) ∧ (p3 → (False → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154322220186621325707855083594 : (((False ∨ ((((p5 ∨ p1) → p4) ∨ (((p1 → p5) → p1) ∧ True)) → (p1 ∨ (p5 → p5)))) ∨ p3) ∧ (p2 ∨ ((False ∧ True) ∨ (True ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651057318650727978132756763493 : ((((((p1 → (False ∨ p1)) → p3) ∧ (((False → (p5 ∨ p2)) → (((p1 → (True → p3)) ∨ (p5 ∨ False)) → p3)) → p4)) ∧ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39327401904410123801081747459 : (((p2 ∧ (((p5 ∧ ((((False → True) ∧ (p5 → ((p1 ∨ (False → True)) → p2))) → p1) ∨ p5)) ∨ p3) ∧ (p5 → (p1 ∧ p3)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81307953119404983309059300346 : (((((True → True) → (((((False → p2) ∧ ((p4 → ((p5 ∨ True) ∨ True)) → True)) ∧ p2) ∧ True) ∧ p4)) ∧ p3) ∨ ((p1 ∧ p4) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58458888879191927717606951026 : (((p3 ∨ p3) ∧ ((p2 → (p1 ∨ (p1 ∧ p3))) ∧ (((((p1 → ((p5 ∧ p5) ∧ False)) ∨ p4) ∧ (p3 ∧ p1)) → True) → (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154302679061910534566545623118 : (((p2 ∧ ((((((False ∧ True) → (p5 → (p5 → (p2 ∨ False)))) ∨ False) ∧ p3) ∨ p5) ∧ True)) ∨ True) ∧ ((p1 ∨ (p4 ∨ (p1 → p4))) ∨ True)) := by
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
theorem thm_5_vars_619477310312134520771529869956 : (((((p4 ∨ (p2 ∨ False)) → ((True ∧ False) ∨ (((False ∨ False) ∧ p4) ∧ ((p4 → ((p1 → (True ∧ (False → False))) ∧ False)) ∨ p5)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_58121121322606714931904164085 : (((p2 ∧ True) ∧ (((p1 → ((((p5 ∨ p2) → True) ∨ p2) ∧ p3)) ∨ p3) → ((p3 ∧ (p2 → p1)) ∧ (True → (p4 ∧ (p3 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137416281666756125491014358583 : ((p4 ∧ ((p2 ∧ (p5 ∧ (False ∧ (((p4 ∧ (p5 → (True → True))) → p3) ∨ ((p3 ∧ p2) ∧ (p4 ∨ p3)))))) ∧ False)) ∨ ((False → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218920836787919391170812669734 : ((p3 ∧ (True ∧ (p3 ∨ p4))) → (((p4 ∨ ((p1 → (((p3 ∨ p4) ∨ p2) ∧ p4)) ∨ ((p5 ∨ p2) ∧ p4))) ∧ (p1 ∨ p2)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150824252599867422766584615926 : ((((p4 ∧ ((p3 ∨ True) → (((p2 ∨ (True ∧ (False → p2))) ∧ p2) → True))) ∧ ((p4 ∨ False) ∨ p5)) ∨ p4) → (((p1 ∨ False) ∧ p3) ∨ p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44823027260441874642902849684 : ((((p1 → (p4 ∧ p5)) ∧ (((((p1 ∧ p2) ∨ p1) ∧ (p1 ∨ p5)) ∨ (p3 ∧ ((p3 ∧ (p2 → (p2 ∧ True))) ∧ p1))) → p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257110385352598659122601800553 : ((p2 ∨ False) → (p4 ∨ (p4 ∨ (((p2 ∨ (False ∨ p5)) → (p4 ∧ p1)) ∨ ((p4 ∧ (((p1 ∧ p3) ∧ (p1 ∨ p5)) → p5)) ∨ (p2 ∨ False)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56019821956690121184488713363 : (((((p4 ∨ p1) → False) ∨ p3) ∨ ((p4 ∧ p2) → ((((p3 ∧ (p5 ∧ False)) ∨ p4) ∧ p2) ∨ (((p5 ∧ p1) ∨ (p1 ∧ p2)) ∧ p5)))) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768659037818276505288293035494 : (((p5 ∧ (((p3 ∨ p2) → (p3 ∧ ((((True → p1) → p4) ∨ p4) → True))) → ((False ∨ (((p2 ∧ True) ∨ p4) → (p2 ∧ False))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44569273105515470827846978787 : ((((p2 → ((((False ∨ p5) ∧ p1) → False) → p3)) ∧ ((((p4 ∨ True) → p4) ∨ True) → ((False ∨ ((p1 ∨ p5) ∧ p3)) → False))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734799216082115688870681161504 : ((((p2 ∨ p1) ∧ (((p2 → ((((((p4 ∧ True) ∧ ((False → ((p3 → p4) ∧ True)) ∧ p2)) ∧ p5) ∧ p3) ∧ False) ∨ p4)) ∧ p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309718809762134894222151834084 : (p2 ∨ ((False ∨ ((((False ∨ (p5 ∨ (p2 ∧ (p4 → False)))) ∨ p5) ∧ ((p5 ∨ p2) ∨ (p4 ∧ p1))) → (p2 → p4))) → ((p3 → p4) ∨ True))) := by
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
theorem thm_5_vars_138033179624849993397381696639 : ((True → (((p2 → (((p3 ∧ p5) → False) ∧ ((p1 ∨ p5) ∧ p2))) ∨ (p3 → (p4 → False))) → ((False ∨ p3) → p2))) ∨ (True ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136706403555799912692032531098 : (((p1 ∧ p5) ∧ ((((p3 ∨ ((p4 → (p5 ∧ (True → (p1 ∨ False)))) ∨ p3)) → (p4 ∧ (p3 → p1))) → p2) → p2)) ∨ ((p5 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354623344703164705434233966793 : (p5 → ((((True ∧ p4) ∨ (((p4 ∧ ((p2 → p5) ∧ ((p3 ∧ (p1 ∨ False)) → (p3 ∧ (p4 → True))))) ∨ p4) ∨ (p4 ∧ p4))) ∨ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111071124391886573304998328000 : ((((p4 ∨ (p1 → (p4 → ((((True ∧ (p2 → False)) ∧ p4) ∧ p2) ∧ p4)))) ∨ ((((True ∨ p3) ∧ p5) ∧ p2) → p4)) ∧ p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764608579376594276174465916287 : (((p4 ∧ ((((((p2 ∧ (p2 → p4)) → p1) → (p5 ∨ False)) ∨ (p1 ∧ True)) ∨ (((p3 ∨ p4) → (p2 → (True ∨ False))) ∧ True)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41426979703362332864968605968 : (((((((((p1 → ((False ∨ True) ∧ False)) → p3) ∧ p2) ∨ True) → p5) ∨ p3) → ((p2 ∨ p3) ∧ ((p5 ∧ (False ∧ p3)) ∨ p4))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314830329047425766668398471039 : (p3 ∨ (((p4 ∧ ((((p5 ∨ (p4 ∨ p2)) ∧ p1) ∧ True) → p3)) → False) ∨ ((((False → ((p2 ∧ p2) ∨ p2)) ∨ p1) ∨ (p4 ∧ p5)) ∨ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318468765057062657124268933416 : (p4 ∨ (((((p1 ∧ p3) ∨ p4) ∨ (((p5 → (p5 ∨ p2)) ∨ p1) → (p3 → (p3 → (p1 → p3))))) ∨ ((p4 ∨ p5) ∧ False)) ∧ (p3 ∨ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43635475234274223212845639714 : (((((((((False → ((p1 ∨ p2) ∨ (p3 → False))) ∧ False) → p4) → (p3 ∨ (p5 ∧ True))) → (p2 ∧ p3)) ∨ (p2 → p1)) → p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137868395917131170496543424273 : ((p3 ∨ (True → (((p2 ∧ (False → p4)) ∨ ((True ∨ (p5 → ((p2 ∨ (True → p1)) ∨ p2))) → (p5 → p2))) → p2))) ∨ (p1 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337780736615238442282963343570 : (p1 → ((p2 ∨ ((((p4 → (p3 ∧ (p4 → p4))) → p4) ∨ p1) ∧ ((p3 ∨ p5) ∨ p1))) ∨ (p2 → (((p2 → True) → True) → (p3 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328183525932236005589900565537 : (True → (((((False → (((p1 ∧ p3) ∧ p1) ∧ (p2 ∧ p4))) → p2) → (False ∧ p2)) ∧ (False → ((True ∧ p2) ∨ p5))) → (p4 → (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((False → (((p1 ∧ p3) ∧ p1) ∧ (p2 ∧ p4))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138318710522425503206041424003 : ((p3 → (True ∧ (((True ∧ (p5 ∨ ((((p5 ∨ (p2 ∧ p5)) ∧ False) ∨ (True ∧ (p5 → p1))) ∧ p5))) ∨ p3) ∨ False))) ∨ ((p2 → p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_8833074952681385089763614612 : (((((p1 → (p3 → False)) → (True → ((((p3 ∨ ((False ∧ True) ∨ (p1 ∧ p4))) → p5) ∧ p1) → p4))) → (p3 ∨ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145744806550806377285154097285 : (((p1 ∧ p3) ∨ (False ∨ (((p4 ∧ p3) ∧ ((((p1 ∧ (p3 ∧ True)) ∧ p1) ∨ (p3 ∧ False)) ∨ p5)) → p4))) ∧ (p2 ∨ (p3 ∨ (False → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h18
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111996530703673450458231677860 : ((((p4 → (p1 ∧ (p4 ∨ True))) ∧ (((p4 → False) → (((p3 ∨ p5) ∨ ((p1 ∨ True) → p3)) ∧ (p2 → True))) ∧ p2)) ∨ p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110938880070013217462106723715 : ((((((p5 ∧ p5) ∨ ((p5 → p3) ∧ p3)) ∨ (((((p2 → p4) ∨ p3) ∨ p1) ∧ (p4 ∨ p3)) ∨ p2)) ∧ (p1 → True)) ∧ p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355571940626660243451340015864 : (p5 → (((p5 → ((p1 ∨ (p1 → True)) → (((p4 ∧ (False → True)) → (p1 ∨ p5)) ∧ (p1 → p3)))) ∨ ((p3 ∨ p3) → p4)) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661408817773115442452636604957 : (((((p4 ∨ ((p3 → False) ∧ (True ∧ (((True ∨ (p1 → (p1 ∧ (True → (p5 → p4))))) ∨ False) ∨ p1)))) → (p2 → True)) → (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114592162140926563962731671802 : ((((p2 ∧ p3) ∨ (p2 ∨ (p4 → (p5 → (p5 ∧ ((p3 ∨ True) ∨ (False ∧ p3))))))) ∧ (p1 ∧ ((p1 ∧ p4) → (False ∧ True)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219270421302254583700518736965 : ((p1 ∨ (p4 ∨ (p4 ∨ p2))) → (((p2 → (p4 → ((p3 ∨ ((p3 ∨ True) ∨ ((p2 ∧ p5) ∨ (p5 ∧ p5)))) ∧ (p2 ∧ p1)))) → p5) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328760430894207901595211790655 : (True → ((((((False ∧ p1) ∨ p5) ∧ p3) ∨ p1) ∨ (True ∨ True)) ∧ ((True → ((p4 ∨ False) ∨ False)) → (p2 → ((False → p4) → (True ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822296354325406079505133679015 : (((((((p3 ∨ (p4 ∨ p3)) ∨ p3) ∨ (p4 → (False ∧ True))) ∧ (((p5 → p2) → (((p4 ∧ p5) ∧ (p4 ∧ p2)) ∧ p3)) ∧ p2)) ∧ p2) → p3) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h5.left
        let h10 := h5.right
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h5.left
          let h14 := h5.right
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h15 : (p5 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h17 := h13 h15
          -- We need to get the right conjuct of h17 based on <expert-advice>.
          let h18 := h17.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h5.left
          let h21 := h5.right
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h5.left
      let h24 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h5.left
    let h27 := h5.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h28 : (p5 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h30 := h26 h28
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- One of the premise coincides with the conclusion.
    exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341689173463919107861850536810 : (p2 → (((p1 → ((p1 ∧ (((p1 ∧ p4) ∧ ((p1 → p4) ∨ (((p5 → False) → p4) → False))) ∧ (False ∨ p2))) ∧ p1)) → False) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723640605771030221522820410517 : (((((p4 ∨ p1) → False) ∧ ((((((p5 → p4) ∨ p4) → (((True → (p4 ∨ p4)) ∨ (p1 ∧ (p1 ∧ p2))) → p3)) ∧ p2) → p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723242752758721490053613023694 : (((((p2 → p4) ∨ p4) ∧ (p2 → ((p2 ∧ ((p4 ∨ (p1 ∧ (((False ∨ (((False ∨ p3) → False) → False)) ∨ False) → p4))) ∨ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147250186430910313027471148015 : ((((True ∧ ((p3 ∨ ((p2 ∧ ((False ∧ (p1 → False)) ∧ (p4 → p2))) ∨ p3)) ∨ (p1 ∧ p5))) ∧ p3) ∨ p3) ∨ (((False ∧ False) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613727334209837569989953270102 : ((((((p3 ∨ p2) ∨ (((False ∧ False) → ((p3 ∨ False) → ((p3 ∨ False) ∨ (p2 ∧ (p5 ∧ p2))))) → p5)) ∧ ((p3 ∧ False) ∧ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745858043392541241280565707085 : ((((False ∨ p1) → (p3 → ((((False ∨ (p2 ∨ (p1 → (p2 ∨ ((p4 ∧ (p3 → True)) → ((False → p4) → p4)))))) ∧ False) ∨ p2) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147395500632223398922468091939 : ((((p3 ∧ (p1 → ((p4 ∧ p2) ∨ (p2 ∧ False)))) → (p2 ∧ (p1 ∧ (p4 → (p3 → (True → False)))))) ∨ p2) ∨ (p4 ∨ (True ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758453908591984103620738879402 : (((p2 ∧ ((False ∧ (((p5 ∨ (((p5 ∨ p4) → (p2 → (p2 ∧ p5))) ∨ False)) → (((p3 ∧ p1) → p3) ∧ p2)) ∨ (True → p3))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664887218242959994664661383846 : ((((p2 → (p4 ∧ (p5 ∨ (((True ∨ (p4 → (True ∧ p2))) ∧ (((p3 → (True ∨ p4)) ∨ p1) ∧ (p2 ∧ p1))) → p2)))) → (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62711571114655114540768929014 : ((p4 ∧ (((True ∧ p1) → (((p5 ∧ ((p3 ∧ p1) → (p2 ∨ p1))) ∧ (p5 → False)) ∨ ((p3 ∧ ((p3 ∧ False) ∧ True)) ∨ p2))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341741168975978060364701149100 : (p2 → (((p1 → p1) → ((p4 → (((p2 ∧ p5) ∨ ((p1 ∨ p4) ∧ ((p1 ∨ (p1 ∨ (p4 ∧ p5))) ∨ True))) ∨ p2)) → p5)) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37869194300267265980415784007 : ((((p5 → (((((((p1 ∨ p4) ∨ p4) → p5) → ((((p5 → (p2 → p5)) ∨ p1) ∨ p2) ∧ p5)) ∧ p4) ∧ p1) ∨ p5)) → False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734951427534328214370338959179 : ((((p2 ∨ p4) ∧ (p3 ∨ ((False ∨ p4) ∧ (p5 ∧ (p2 ∨ ((p4 ∨ (((True ∨ True) ∧ (p3 ∨ ((p3 → True) ∧ False))) ∨ False)) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160118064139258370858498624318 : (((p4 → ((p2 ∧ ((p5 → p3) ∨ (False → (True ∧ p4)))) → ((p3 ∧ (p3 → False)) ∨ False))) → False) → ((p1 → (p3 ∨ False)) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118836529463060028021924025146 : ((True → (((((True → (p1 → ((True ∧ (p3 ∧ False)) → p5))) ∨ p4) ∨ (((p2 ∧ p4) ∧ p2) ∨ p4)) → p5) → (p2 ∧ p4))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52960884928313465427171624427 : ((((p4 → (((p5 ∨ False) → ((p3 → p4) → p4)) → p5)) ∨ p3) ∧ ((((p1 → (True ∨ (p2 ∨ p1))) → (True ∧ True)) ∧ True) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



