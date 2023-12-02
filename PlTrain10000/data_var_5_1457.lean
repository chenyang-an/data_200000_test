variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138162350276121343123309434000 : ((p1 → (((p1 ∨ False) ∨ (p3 ∨ (p5 → ((True ∧ (p1 → p1)) ∧ (p3 ∨ ((p1 ∨ p5) ∨ p2)))))) → (p5 → False))) ∨ (p1 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615761860043607270450420458453 : (((((True → ((((((False ∧ True) ∨ p5) ∨ p2) ∧ (p4 ∨ p2)) ∧ p5) ∧ p5)) ∧ (False ∨ ((p1 ∨ p2) → (p1 ∧ (True → True))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_147690583694909134061754582351 : ((((p2 ∨ (p2 ∨ ((p5 ∧ p2) → ((True ∨ ((p5 → p5) ∨ p2)) ∧ p1)))) → ((p5 ∨ True) ∧ p4)) → p5) ∨ (p4 ∨ ((p1 ∧ False) → p4))) := by
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
theorem thm_5_vars_179425018124404348655573542468 : ((p4 ∨ ((p2 ∨ (True ∨ p3)) ∧ ((p3 ∧ ((p3 ∨ False) ∨ p2)) ∧ p2))) ∨ (p1 ∨ (((p1 → True) ∨ (p3 ∨ (p3 → p5))) → (p3 → True)))) := by
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
theorem thm_5_vars_68110020256684302443921212342 : ((p2 → (p2 → ((((((((((False ∧ p3) ∧ False) ∨ p2) → ((p3 ∨ True) → True)) ∧ (p4 → p4)) ∧ p5) ∧ p4) → False) ∨ p2) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64782669898402749074926047870 : ((p2 ∨ ((((p1 ∨ (((True ∨ ((p2 ∨ ((p4 ∧ p4) ∧ False)) ∧ (p3 → True))) ∨ False) ∧ (p3 ∧ p1))) ∨ p4) ∨ (p2 ∨ True)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190208723303892290244361163561 : (((True → (((p4 ∨ p2) → (False → False)) → False)) ∧ False) ∨ ((p3 → (((p2 ∨ (p4 ∨ p3)) ∨ (p5 → (p5 ∨ False))) ∨ p1)) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342783610279503070627053808329 : (p2 → (((p4 ∧ ((p2 → (False ∨ p5)) ∧ False)) → True) → (((p1 → ((((p3 → (False ∨ p3)) → p3) ∨ p4) ∨ False)) ∨ (p5 ∧ p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194087060855341729438748173261 : ((True → (p3 ∧ (p4 ∧ ((False → (p1 → True)) ∧ True)))) → ((((p4 → p5) ∨ p4) → ((((p5 ∨ p4) ∧ (True ∨ p1)) ∨ p4) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246408631117582307970062075924 : ((p5 ∧ True) ∨ ((p1 ∧ p1) ∨ ((((p4 ∨ p1) ∧ (((p2 ∧ (p5 → ((p4 ∨ (p5 → False)) → p5))) ∨ (p1 ∧ p4)) ∧ True)) ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263081179944158373389623892924 : (True ∧ (((((p1 → (p4 ∨ (p4 → ((p4 → p5) → (p4 ∧ p2))))) ∧ p2) → ((((p5 → p5) ∨ True) → p4) ∨ True)) ∨ p2) ∨ (p2 ∨ True))) := by
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
theorem thm_5_vars_191349001111408436737375197557 : (((p1 ∨ p2) ∨ ((False → (p1 ∧ (False → True))) → p2)) ∨ ((((True ∨ p2) ∨ False) ∨ ((p2 ∧ ((True ∨ False) ∧ True)) ∧ False)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299701267417461589700505285253 : (False ∨ ((((p3 ∨ (p1 → (((False ∨ p3) ∧ (p4 ∧ False)) ∨ p4))) ∧ (p3 → False)) ∧ (((p3 ∨ p4) ∨ p1) ∨ ((p4 ∨ False) ∧ True))) → p4)) := by
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
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h10 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h11 := h5 h10
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h25 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h26 := h5 h25
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h27
      case inr h28 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h29 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h30 := h21 h29
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h34 =>
            -- False on the left can always be used.
            apply False.elim h34
          case inr h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h33.left
            let h37 := h33.right
            -- False on the left can always be used.
            apply False.elim h37
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h43 =>
        -- False on the left can always be used.
        apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801265672072171557973293392562 : (((p2 → ((p2 ∨ (True ∨ (True ∨ ((p4 ∧ p2) ∨ ((True ∨ p4) → ((p5 ∨ p3) ∨ p3)))))) → (p4 → (((p5 ∨ p3) ∨ True) ∧ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792664373072323382314764632573 : (((True → (((p5 ∧ (p5 ∧ True)) → (p3 ∨ p1)) → ((((p3 ∨ True) → ((((p3 → p3) ∧ p3) → p5) ∨ p2)) ∨ True) ∨ (p2 ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347198020074520893162154200511 : (p3 → ((((p5 → False) ∨ (p3 ∧ p4)) ∨ (((p4 ∧ p1) → p3) → p5)) ∨ ((False → ((p2 ∧ (p5 ∨ (p4 ∨ True))) → (False → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304709867530333793130725543914 : (p1 ∨ ((((((p4 ∧ False) → True) ∧ (((p3 → False) ∨ p4) ∧ (p4 → (p2 ∨ p2)))) ∨ ((p4 → True) → p1)) ∨ (p1 ∨ True)) ∨ (p4 ∨ p2))) := by
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
theorem thm_5_vars_37535692575196185485213888923 : ((((p3 ∧ ((((p3 → (p2 ∧ ((p1 ∧ (p1 ∨ (p5 ∧ (p3 → p1)))) ∨ False))) ∧ (True ∧ p2)) → p3) ∨ (p4 → False))) ∨ False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79917835787477328476687659587 : (((True → ((p3 → True) ∧ ((p3 ∨ (((False ∧ True) ∨ True) ∧ False)) ∧ ((p4 ∧ ((p2 ∨ (p3 ∨ p3)) → True)) ∧ False)))) ∨ (False ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187338812258300204107888922027 : ((p2 ∧ ((p5 ∧ (p2 ∨ p1)) ∧ (((p3 ∨ p3) → True) ∨ p5))) → ((((p1 ∨ (False ∨ ((p4 ∨ True) ∨ False))) ∨ False) ∨ p1) ∨ (True ∨ p2))) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214391280526006896041940669907 : (((False → (p1 ∧ True)) → p2) ∨ (((False ∧ ((((p2 ∨ p1) ∨ (p3 ∨ (p2 ∨ (p1 → p5)))) → (False → p1)) ∧ p5)) ∧ p5) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713348511596969202800177502681 : ((((True → (p4 ∧ ((p4 ∨ p5) → p5))) ∨ ((((p1 ∨ (False → (p1 → p1))) → p3) ∧ (p3 ∧ (p1 ∧ p2))) ∨ (p5 ∨ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234543072284821836319068616372 : ((p3 → (False ∧ p1)) → (((p5 → p1) → (((False ∧ (False ∧ (p4 ∧ p2))) → False) → (((False ∧ (p4 ∧ p5)) ∨ p1) → p2))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346296658882007085582337327892 : (p3 → (((((p5 ∧ ((p3 → p5) ∨ p3)) → (p4 → p5)) → (((p1 ∨ p2) ∧ p1) → ((p4 → (p5 ∨ p5)) ∨ p3))) ∨ True) ∨ (True → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707460531149789325374611012798 : (((((p4 ∨ (p2 ∨ False)) ∧ (p3 → (True ∧ p5))) ∨ (p5 ∧ (((((False → p1) → (False ∧ (p4 → (p3 ∧ p1)))) ∨ p2) → p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341677698171906351990353689316 : (p2 → (((p5 ∨ ((((p4 ∧ (p4 ∨ (p5 → (p5 ∨ (p1 ∨ (p5 ∧ (False ∨ (p2 ∧ p4)))))))) ∧ p1) ∨ False) ∧ p2)) ∨ p2) ∨ (p4 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104636857130649935841818357583 : ((((p3 ∨ p3) ∨ ((((p2 ∨ p3) ∧ p5) ∧ ((p4 ∧ p1) ∧ (p1 → p5))) ∨ (p5 ∨ (p2 → (False → p4))))) ∨ (p2 → p1)) ∧ (False ∨ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68671400683084110453569756274 : ((p4 → ((p5 ∨ (True → (((((p3 ∨ ((True ∨ p1) → (p1 ∨ p2))) → p3) → (False ∨ (True ∧ p4))) ∨ (False → p1)) → p4))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797869240729918924127832741197 : (((p1 → ((((False ∧ p5) ∨ ((p4 ∨ (p4 → (((p1 ∨ p2) → p2) ∨ p2))) → (p4 ∧ p5))) ∨ (True → (p4 ∨ p1))) ∨ (p5 ∧ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44367517978747045915678586692 : ((((((False ∨ p4) ∨ (p2 ∨ p3)) → ((p3 ∨ (True → (True ∧ p4))) → True)) ∧ ((((False ∨ p4) ∧ p4) ∨ (p4 → p4)) ∨ True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179029438154717277315128615173 : (((p3 ∨ p2) → ((((p1 ∨ (False ∨ p1)) ∨ True) ∧ True) ∧ (p5 → True))) ∨ (((p1 ∧ p3) → (p5 → (p2 ∨ ((p2 ∨ p4) ∨ p3)))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125850981810591368652909011519 : (((False ∧ True) → (((((p1 → p3) → p5) ∨ p5) ∧ p2) ∧ ((p4 → ((p2 → ((p2 → p3) ∧ p3)) ∧ (p2 → p1))) ∨ False))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692532389786022036192538289140 : ((((((((p2 ∧ False) → True) ∨ ((False ∧ p5) ∧ p5)) → p5) → (False ∨ p1)) ∧ ((p5 ∧ ((p4 ∨ (p5 ∨ False)) ∧ p5)) ∧ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77044854031650858706977242825 : ((((p2 ∧ (p5 ∨ (p5 → (p1 → p2)))) → (p5 ∨ (True → ((((True → (p3 ∧ p5)) ∨ p5) ∨ True) ∨ (False ∧ (True → p4)))))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p5 ∨ (p5 → (p1 → p2)))) → (p5 ∨ (True → ((((True → (p3 ∧ p5)) ∨ p5) ∨ True) ∨ (False ∧ (True → p4)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165601927133417536509665325449 : (((((p4 → (p1 ∨ p4)) ∧ p2) → (p2 → p1)) → (p4 ∨ ((p3 → p3) ∧ (p4 ∧ False)))) ∨ ((p2 ∧ (p2 → (False ∧ (p2 ∨ p5)))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751791740965482102597731542586 : (((True ∧ (False ∨ (((p2 ∧ (p2 → ((p5 ∧ ((p3 ∨ p3) ∧ (((p4 ∧ False) ∧ ((p5 → p1) ∧ False)) ∨ p1))) ∨ p4))) ∨ True) ∨ p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_49117421886627489535574768929 : ((((((False ∨ ((p2 ∧ (p1 ∨ ((p1 ∨ p5) ∧ True))) ∨ p3)) ∧ p2) → False) → (((p2 ∧ True) ∨ False) → p5)) ∨ ((True → False) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225445152694285605897377313310 : (((p4 ∨ True) ∧ p1) ∨ ((p3 ∨ p5) ∨ (p2 ∨ ((((True ∧ p1) ∧ p1) → (p5 → (False → ((p1 ∨ p4) ∨ ((p1 ∨ p4) ∧ p3))))) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49640354754135585812846805611 : ((((p4 ∨ ((p5 ∧ p3) → p2)) ∧ ((p3 ∨ ((p2 → True) → (((p2 ∨ True) → True) ∧ p3))) ∧ (p4 → p1))) → ((p4 ∨ True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678435637752585067852583591645 : ((((((p5 ∨ p4) ∧ (p4 ∧ p3)) ∨ (p4 ∧ ((p1 ∨ ((True ∨ p2) ∧ p4)) → ((p2 ∨ p2) → p4)))) ∨ (((True → p4) ∧ p1) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138346799211410684853221785662 : ((p4 → (((p2 → (p1 ∧ (p5 ∨ (p4 ∧ p3)))) ∧ ((((p3 ∨ ((False ∨ p4) → False)) ∧ p3) ∧ p1) ∨ True)) ∨ p3)) ∨ ((p2 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300667315926463781139636284646 : (False ∨ ((((p2 ∧ (p1 ∨ p4)) → (((p3 → False) ∨ (p4 → p2)) → (p1 → (p4 → p3)))) ∨ True) ∨ (((False ∨ False) ∨ (p3 ∨ p2)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197263313593281117207316805278 : (((((p1 → p5) ∧ p3) ∧ (True → p5)) → p4) ∨ ((((((True ∧ True) ∨ (p2 ∨ p1)) ∨ False) ∨ (p3 ∧ (p2 ∧ p4))) → (p5 ∧ False)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∧ True) ∨ (p2 ∨ p1)) ∨ False) ∨ (p3 ∧ (p2 ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206926295352223264547944396487 : ((((p3 ∨ (True → p3)) ∨ p2) ∧ True) → ((p1 ∨ (((p1 ∨ p5) ∨ (p4 ∧ True)) → p5)) → (p2 ∨ (p1 → (((p4 → p3) ∨ False) ∨ p3))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h23 := h20 h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33501818839084634067709518265 : ((p4 ∨ ((False → True) ∧ (((p2 ∧ (True → p2)) ∧ ((p5 ∧ (p2 → p5)) ∧ p4)) ∨ (((p3 ∧ p1) → p3) ∧ ((False → False) ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134718363126825544409564707358 : (((((p4 → p4) ∨ p1) ∨ ((p1 ∧ ((p5 ∧ (False ∧ True)) ∧ p5)) → (p2 → (p3 ∧ ((False ∧ False) ∧ p4))))) → p4) ∨ ((p4 ∧ True) → p4)) := by
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
theorem thm_5_vars_616464974934265316970351448389 : (((((((p3 ∧ p1) ∨ p2) ∨ (False ∨ ((p2 → p1) → (False ∧ p3)))) → ((((True ∨ ((p5 → p4) ∧ p2)) ∧ p1) ∧ p1) ∨ p5)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135829668007133159325750000239 : (((((p2 → (p5 ∧ p4)) ∧ (p2 ∨ p3)) → (p2 ∧ (False ∨ p3))) ∧ ((((True ∧ p1) ∧ True) ∨ True) ∨ (p1 → False))) ∨ (False → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45702230915349150502547182534 : (((True → ((((p2 → (True ∧ p2)) ∨ (p5 ∨ ((p1 ∨ (p3 → True)) → (((p5 → p3) → (p3 ∨ True)) ∨ p1)))) → p2) ∨ p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307123224953168282714554650028 : (p1 ∨ (False ∨ ((p4 ∨ (((p4 ∨ ((p2 ∧ (False → p3)) → p5)) ∨ True) ∨ ((p4 ∨ p1) ∨ ((True ∧ False) ∧ (p3 → (True ∧ p2)))))) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673302223914301518927202677823 : ((((((((p4 ∨ p2) ∨ p1) ∧ False) ∧ (p2 → p2)) → (p3 ∨ (p3 → (((p2 ∧ p5) ∧ (p2 ∧ p1)) → p3)))) → ((p4 ∨ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49210680355190497902010325823 : ((((True ∧ False) ∧ ((((p2 ∨ ((p4 ∧ (True ∧ p3)) ∧ ((False → p3) ∧ p3))) ∨ p5) → (p4 ∧ True)) → p4)) ∨ ((p3 ∧ p2) → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_38483309354957568265901057181 : (((((False ∧ True) ∧ (((p2 ∧ (p5 ∨ p3)) ∧ p1) ∧ (p3 ∧ p5))) ∧ (p3 ∨ ((((p4 → True) ∧ p2) ∧ (p2 → True)) ∧ p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172052464248311491882295336640 : (((((p4 ∨ False) ∨ (((p5 ∨ (p2 ∨ p3)) ∧ p5) ∧ p3)) ∧ True) → (p1 ∨ False)) ∨ ((False ∧ ((p3 ∧ p3) ∨ (False ∨ (p2 → False)))) → p1)) := by
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
theorem thm_5_vars_47841200114933012890140725515 : ((((p3 ∧ (p4 → (False ∧ ((((False ∨ p4) ∨ (((p3 → p1) → True) → (p3 → p3))) → (p2 ∨ True)) → p3)))) → True) → (p1 → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69964200012873703932225721725 : (((((((True → ((((((p4 → False) ∨ p3) ∧ p2) ∨ True) ∧ False) ∧ p2)) ∧ (p4 → (p1 ∧ (False ∨ p5)))) → p5) ∧ p3) → p1) ∧ p3) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True → ((((((p4 → False) ∨ p3) ∧ p2) ∨ True) ∧ False) ∧ p2)) ∧ (p4 → (p1 ∧ (False ∨ p5)))) → p5) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656869989185958965976111537348 : (((((p2 ∨ (p2 ∨ (p5 → True))) ∧ ((p4 ∧ ((False ∨ p4) → p3)) → (p1 ∧ ((p1 ∧ p2) ∧ (p4 ∧ (False → p3)))))) ∨ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135877331336227272233965097400 : ((((p4 ∨ p2) ∨ (True → (((p2 → False) → True) → (p4 → p2)))) ∨ (True → ((False ∧ ((p3 → False) ∧ p5)) → p3))) ∨ ((p4 → False) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47244102313250840297064764452 : ((((((True → p1) ∧ (p2 ∧ p2)) ∨ True) ∧ ((((True ∨ False) ∧ (True → ((p5 ∧ p1) ∨ p4))) ∨ p4) → (False ∧ False))) ∨ (p4 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303062857407145130376011681783 : (False ∨ (p2 → (((p2 ∧ ((((False ∨ p5) ∧ p1) ∨ (p3 ∨ ((True ∧ True) ∨ p3))) ∧ p1)) ∧ p2) ∨ (True ∨ (True → ((p4 → p1) → p3)))))) := by
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
theorem thm_5_vars_228737650905838894078932714862 : ((p2 ∨ (p3 → p5)) ∨ (((p5 → p3) ∧ (((p3 → (((True ∧ False) → ((p2 → p3) → p4)) ∨ p4)) → p3) ∨ p2)) ∨ (p4 ∨ (True ∨ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206141737007304226218956668037 : ((p4 ∧ (True → ((p4 ∧ True) ∧ p4))) ∨ ((((False ∧ ((p1 → (p2 ∧ p4)) → p5)) ∧ (p5 → p2)) ∨ True) ∨ (((p2 ∧ p2) ∨ p2) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205240012868501988230381492388 : ((((p3 ∧ p2) ∨ p3) ∨ (p4 ∨ p1)) ∨ ((p4 ∨ True) ∨ ((p2 → (p4 ∧ (True → (((p1 ∧ p5) ∨ False) → (p5 → (p1 ∨ p3)))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165773813422332458371369549598 : ((((False → (p2 ∧ p4)) → True) → (((p2 ∧ ((p2 ∧ p2) → p4)) ∧ (p2 ∨ p5)) ∨ p2)) ∨ (((((p1 ∨ True) → p1) ∨ p2) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50476282464881856455426002443 : (((p1 → ((False → (False → True)) → (p3 ∨ ((((((p4 ∧ p5) → False) ∨ True) ∧ True) ∧ True) ∧ p3)))) ∨ (False → (p3 ∨ (p5 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55635130552410752646100740467 : (((((p5 ∨ p4) ∧ False) ∧ p4) ∧ (p4 ∧ ((True ∧ ((True ∧ (False ∧ ((p2 → (p5 → True)) ∨ (True ∧ True)))) ∨ p1)) → (p5 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354795098116387354018674397032 : (p5 → (((p5 ∧ ((False ∨ (False → p3)) → False)) ∨ ((((p4 ∧ True) → ((p3 ∧ p5) → True)) → ((p5 ∧ p2) ∨ False)) ∨ (p3 ∨ p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175360437198163704380481555141 : ((p5 ∨ (p5 ∧ (((((p1 → p5) ∨ p1) → False) ∨ ((p4 ∧ True) → True)) ∨ p5))) → (((p2 ∨ (p3 ∧ False)) ∧ (p1 ∨ (p4 ∧ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81138220889963737202532130288 : ((((True ∨ False) → ((p4 ∧ False) ∧ (((False → p5) → ((p4 ∧ (p1 ∧ False)) ∧ (p2 ∧ p5))) ∧ (p4 → False)))) ∧ (p2 ∨ (p4 ∧ p5))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254357505525727568993594149781 : ((p2 ∧ p4) → (((((False → p2) ∧ p3) ∧ p4) → True) → (((((p4 → (False → (False ∨ (False ∧ True)))) → p5) → p2) → p1) ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703178782772573983800242370836 : ((((True ∧ (((p5 ∧ True) → (p3 → (p5 ∧ p3))) → False)) ∨ (p5 → (((False → ((p1 ∧ (True ∧ p2)) ∨ p2)) ∨ (False → p5)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227678584869042329370659312945 : ((False ∧ (p4 → p2)) ∨ (p5 → ((True ∧ ((False → p5) → False)) ∨ (((False ∧ ((p1 ∨ (p4 ∨ p2)) → p3)) ∨ p5) ∧ (p2 → (p2 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40475408241610882248980138513 : (((((p3 ∧ p3) ∧ (False ∧ ((p5 ∨ p1) ∨ (True ∧ (((p3 → ((p4 ∧ p5) ∨ (p4 ∧ p5))) → True) ∨ (p1 ∧ p1)))))) ∨ True) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200856946909283967607946185552 : ((True ∨ (p1 ∧ (p5 ∨ ((p3 → p4) ∨ p5)))) → ((False ∧ (((p5 ∨ False) ∧ (((p2 → True) ∧ p3) → p1)) ∧ True)) ∨ ((p4 ∧ p3) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
theorem thm_5_vars_257681976606144124754873354896 : ((p3 ∨ p3) → ((((p3 ∧ (True → (((p4 ∨ p2) ∨ (p5 ∨ True)) ∧ (False ∨ False)))) ∧ (p2 → (p3 → (p4 ∧ p3)))) ∧ p4) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114794925152638740838137215795 : (((((p5 ∨ ((p1 ∨ (True ∧ p4)) ∨ p2)) ∨ (True ∨ p1)) → (p1 ∨ p4)) ∧ (p5 ∧ ((p4 ∧ p5) ∧ (p5 ∧ (p3 ∧ p1))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67480288184489326095314861059 : ((p1 → ((((p2 → ((p1 ∨ (p1 ∨ p5)) ∧ p2)) ∨ p5) → ((p1 ∧ True) → False)) ∨ ((p5 ∨ ((p1 ∨ p1) → p1)) ∨ (True → p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205428283136328293797984402062 : (((p4 ∧ (p5 → True)) → (False ∧ False)) ∨ ((p4 → ((p5 → (p5 ∧ (p4 ∨ p5))) → (p1 ∨ (p4 → ((p2 → p3) → (p5 ∧ p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53918776943490189554596497841 : (((p1 ∨ (p5 → ((False ∧ p3) ∨ ((p1 ∧ p5) ∨ False)))) ∨ (p4 ∨ (((p1 ∧ ((((False → p1) ∧ True) → p1) → False)) → p1) ∨ False))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217596289915532490927169461578 : ((((True → p3) ∨ p5) → False) → ((p4 ∨ (p1 → (p2 ∧ p1))) → (((p5 → p4) ∨ p4) ∧ (p2 ∨ (((p5 → (True ∨ False)) → p4) ∨ True))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((True → p3) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_157022070642211888291226610753 : ((((False → True) ∧ (p1 ∧ ((p3 ∨ (((True ∧ p4) → (p1 ∨ False)) → (p5 → p4))) ∧ p1))) ∨ p1) ∨ (((p1 ∨ True) ∧ True) ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228418844104188400353780708701 : ((False ∨ (p3 ∧ False)) ∨ ((((p1 ∧ p2) ∧ ((p5 ∨ False) → p3)) → p1) ∧ (((p1 ∨ (True ∨ False)) → False) → ((False ∧ p4) ∧ (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h11 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138415024253890998570971268850 : ((p5 → ((p2 ∨ (False ∨ ((p2 ∧ ((((p4 → (p1 ∨ False)) ∧ True) ∧ p3) → (False ∧ (p1 → False)))) ∨ p4))) ∨ p5)) ∨ ((p2 → True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48173955345995249133590467604 : ((((p2 → False) ∧ (((((p2 ∧ ((p5 ∧ p2) → ((p5 → (p5 ∨ p3)) → p2))) → False) ∨ p2) ∨ (p2 ∧ p5)) → False)) → (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175900436316893849768047534295 : (((((p1 ∧ p1) → True) → (p1 → (((p4 ∧ p1) ∨ p1) ∨ False))) ∨ p3) ∧ ((p4 ∨ (p2 ∨ (False ∧ ((False → (False ∧ p1)) → p3)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43294329418486092721528470515 : (((((False ∨ ((p3 → ((True ∧ (p2 → True)) ∧ ((p1 ∨ p3) ∧ (p1 ∨ False)))) ∧ ((p4 ∨ (p3 → p5)) ∨ p1))) ∧ p3) ∨ False) → p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h11 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h12 := h7 h11
          -- We need to get the right conjuct of h12 based on <expert-advice>.
          let h13 := h12.right
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h18 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h19 := h7 h18
          -- We need to get the right conjuct of h19 based on <expert-advice>.
          let h20 := h19.right
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42936475353660634174553559121 : (((p4 → ((((True ∨ p5) → p4) → ((False ∨ p5) ∧ ((p4 ∨ (p3 → p5)) → False))) ∨ ((p5 → (False ∨ (p4 → p4))) ∨ p5))) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740928429741927693586356782018 : ((((p3 ∨ p2) ∨ (True ∧ (((p3 ∧ (p4 → (((((p4 ∧ p1) ∨ p4) ∧ (p4 → False)) ∧ p4) ∨ (False ∨ p2)))) → (p1 ∧ p1)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45878818403877025317563712851 : (((p3 → (((False → p5) → False) ∧ ((p5 ∨ (False ∨ (((False ∨ False) ∧ (p1 ∨ p2)) → (p5 ∧ p3)))) → ((False ∨ p3) ∧ p3)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329381667646526833075681511792 : (True → ((p2 → (p1 ∧ p4)) → ((p1 ∨ (((p5 → p2) ∧ p2) ∧ (((p2 ∧ p2) ∨ (False → True)) ∧ p2))) ∨ (((p4 ∧ p5) → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167280833052268110722544279755 : (((((((((p1 ∨ True) ∨ p1) ∧ p4) → p3) → p3) ∧ ((p5 ∨ p1) ∧ p2)) ∨ True) → False) → (False ∨ ((True ∧ False) ∨ (p3 ∨ (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p1 ∨ True) ∨ p1) ∧ p4) → p3) → p3) ∧ ((p5 ∨ p1) ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110920941325390474560935566130 : ((((True → (p4 ∨ (((True ∧ p2) ∨ (((p3 → ((True → True) ∨ p4)) ∧ (p4 ∨ p1)) → (p4 → p2))) → p5))) → p3) ∧ p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308703875847278321519813881681 : (p2 ∨ ((p4 ∨ ((p1 ∧ ((((((p2 ∧ p5) ∧ p3) → (p3 → p5)) ∧ False) ∨ False) → ((False ∨ p4) ∨ p5))) ∨ ((p5 ∧ False) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336768438037195867896562236845 : (p1 → (((True ∨ p1) ∧ (p1 ∧ ((((False ∨ ((p4 → False) → p3)) ∨ (p2 ∧ p1)) → ((p4 → ((p2 ∧ p3) ∨ p4)) → p4)) ∧ p2))) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∨ ((p4 → False) → p3)) ∨ (p2 ∧ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p4 → ((p2 ∧ p3) ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h4.left
    let h17 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : ((False ∨ ((p4 → False) → p3)) ∨ (p2 ∧ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h19
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (p4 → ((p2 ∧ p3) ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h22
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165173936174796935470544578296 : (((p4 ∧ ((p2 → (p4 ∨ (((True → p3) ∨ (p5 → p4)) ∧ p2))) ∨ p4)) ∧ (p2 ∧ p5)) ∨ ((p2 ∧ ((p5 ∧ False) ∨ (p5 → p2))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344951833809785144755299652099 : (p3 → ((((False → p2) ∧ (((p1 ∧ p2) → p5) → (((((False ∧ (((True ∨ p5) ∨ p1) → p1)) ∨ p3) ∨ p3) ∧ True) ∨ p2))) ∨ False) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745406662531230777547383230051 : ((((p5 ∧ p4) → ((p1 ∧ ((p3 → p5) ∧ (p5 → ((p2 ∧ p3) ∨ True)))) ∧ (((False ∧ False) ∨ ((p3 ∧ p4) ∧ (False → p1))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601661531325458625635830155947 : ((((p3 ∧ (False ∨ ((p5 ∨ True) → (False ∨ ((((p2 → p3) → p4) → (True ∧ (p3 ∨ (False ∧ (p2 ∨ p2))))) → (False ∨ True)))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58126957778642677464798159412 : (((p2 ∧ False) ∧ ((p3 ∨ (((p4 ∨ p1) ∨ p5) ∧ p5)) ∧ (((((False ∨ (p4 ∨ p5)) ∧ False) ∨ (p2 ∧ (p3 ∧ True))) ∧ p5) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586574315500480521681196948596 : ((((((False ∧ True) ∨ ((((p2 ∧ p2) ∨ True) ∨ (((False ∧ True) ∧ p3) ∨ ((False ∨ True) ∧ ((p3 ∧ p1) ∨ True)))) ∧ p2)) ∧ p1) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



