variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137381347148886830204267992373 : ((p3 ∧ ((False ∨ (False ∧ ((p5 ∨ p4) ∧ False))) ∨ ((((True ∨ (p4 → (True ∨ False))) ∧ (p2 → p1)) ∨ p3) ∨ p3))) ∨ ((p1 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126832885021296199979240977189 : ((p5 ∧ ((((p4 ∨ (p2 → p2)) ∨ (((p4 → p1) ∧ p4) ∧ (True → p2))) ∧ p5) → ((p1 ∧ (p5 ∧ p4)) ∧ (p1 ∧ p4)))) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ (p2 → p2)) ∨ (((p4 → p1) ∧ p4) ∧ (True → p2))) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397760093640216126593754010401 : ((((p3 ∨ (((True ∧ ((p3 ∧ (((False ∨ p4) ∧ p4) → (p3 ∨ p2))) → (p5 ∧ (p2 → p2)))) ∧ p5) ∧ (p3 ∨ (p2 → p2)))) ∨ True) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174692127474067396041986346181 : ((((p2 → p4) ∨ p4) ∨ (p2 ∨ (((((p2 → p1) ∨ False) ∨ p3) ∧ p3) ∨ p3))) → (((((True ∨ (p3 ∧ p3)) ∧ p4) ∨ p1) ∨ p2) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115643953087452817011338450725 : (((((p5 → (p5 → p1)) ∧ p3) → p4) ∨ (((p3 ∨ p3) → (((p3 → p2) ∧ (p4 → p5)) → (p1 → (p4 ∨ True)))) ∧ p1)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300572357414360499070383394943 : (False ∨ ((p5 ∨ (((p5 ∨ ((False → p1) ∧ (p4 ∧ p2))) ∨ ((p3 ∨ (p2 ∨ p1)) ∨ (p5 ∨ True))) ∧ p1)) ∨ ((p1 → p2) → (True ∨ True)))) := by
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
theorem thm_5_vars_218144102227057885128770453596 : (((p4 → p3) ∧ (p3 ∧ p4)) → (p1 ∨ ((p4 → ((p3 ∧ ((True ∧ False) ∨ (p2 → ((False → ((p4 → True) ∧ False)) ∧ p1)))) ∨ p5)) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164809741279516968871495545407 : ((((p4 ∧ True) ∧ (p1 → ((((p5 ∨ p2) → p3) ∨ (p1 ∧ (p5 → p2))) → False))) ∨ p1) ∨ (p1 → (((False → p1) ∧ p4) → (False ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172839270388852151106977544919 : ((False ∧ (((True ∧ p5) ∧ (((p2 → p4) → (p4 → p5)) ∨ (False ∧ p1))) ∨ False)) ∨ ((False → ((p5 → (p3 → (p5 ∧ True))) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791483270127873492976617891339 : (((True → ((p5 ∧ (True → ((False ∧ (False ∨ ((p3 → ((((p4 ∧ False) → (p1 ∨ p3)) ∨ False) ∧ False)) ∧ p1))) ∧ (False ∨ p2)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_254624722724440176382891229538 : ((p3 ∧ p1) → (p3 → ((p3 → ((p3 ∧ (p2 ∨ (((p3 ∨ ((p4 ∨ p2) → (True ∧ p3))) → False) ∧ p1))) ∨ ((True ∨ p1) ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64101289284243688119194997781 : ((False ∨ (((p1 ∨ p5) ∨ ((p4 ∨ ((False ∨ False) ∨ p4)) ∨ True)) → (p5 ∧ ((p4 ∧ (((False ∧ p3) → True) ∧ (p4 → p2))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328109180563577181143054165917 : (True → ((((p4 ∨ (((p2 ∧ ((((p1 ∨ p4) → p3) ∨ p4) ∨ p1)) ∨ p4) → (True ∧ p4))) → p5) ∧ (p5 ∨ False)) ∨ (False → (p4 ∧ p3)))) := by
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
theorem thm_5_vars_324276608857729184347681586339 : (p5 ∨ ((p3 ∨ (((p5 ∧ p5) ∧ p4) ∧ (p2 ∨ True))) ∨ ((((p3 ∧ True) ∧ (p2 ∨ p1)) ∨ p1) → ((False → (p3 → (False ∧ p3))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322538291790357554146927260751 : (p5 ∨ ((p5 ∧ ((((p5 ∧ p2) ∧ (p3 ∧ ((((False → p1) → (((p5 ∨ p4) → p3) ∧ p5)) → p4) → (True ∨ p2)))) → True) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164709262325716907691790703693 : ((((p3 ∨ (((((p5 → True) ∧ p5) → (False ∧ p4)) → p3) → (p4 ∨ p3))) ∨ p4) ∨ True) ∨ (((p4 ∨ (p3 ∨ (p3 ∧ p5))) ∧ p5) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_500756107391139769634590728484 : ((((p1 ∧ (True ∨ False)) ∨ (p1 ∨ ((p4 → True) → (((p3 ∨ ((p1 ∧ (p4 ∧ p5)) → (p3 ∨ (p1 → p1)))) ∧ (p4 ∨ True)) ∨ True)))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761694592101666087499190801826 : (((p3 ∧ (((p3 ∧ p1) → (p1 ∧ (p5 → (p4 ∨ (p5 ∧ (p4 ∧ ((p2 ∧ (p2 → False)) ∧ (False ∧ (p4 → (False → p4)))))))))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39622541259285698091378579544 : (((p2 ∨ (p2 ∨ ((False ∧ ((p4 ∨ ((p2 ∨ p1) ∨ p2)) ∧ (p4 ∧ True))) ∨ (p2 ∨ ((p3 → ((p3 ∧ False) ∧ p4)) ∨ p2))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263408602143416345751673940724 : (True ∧ ((((p1 ∧ p5) ∨ p4) → (p1 ∧ (((p5 ∧ (p2 ∧ p5)) ∨ (p3 ∧ ((p4 ∧ False) ∨ p4))) ∨ (p4 → p3)))) ∨ ((True → p2) ∨ True))) := by
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
theorem thm_5_vars_654373847278259802360524682048 : ((((((((p5 ∨ (p4 ∨ p4)) ∧ p1) ∨ (True ∨ p1)) ∧ ((p3 ∨ (p3 ∨ (p2 ∧ ((p1 ∨ True) → True)))) ∧ p1)) ∨ p2) ∨ (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789307352308877469561509030491 : (((p5 ∨ (((True → True) ∨ ((((p1 → p5) ∨ p3) ∨ p2) ∧ (p4 ∧ (p1 → (p1 ∨ p5))))) ∧ ((((p1 ∨ p4) ∧ False) → True) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428279217599836107102948062300 : ((((((p2 → (((p3 → p4) → p3) ∨ (((p3 ∨ True) → (((p3 ∧ p1) → False) ∧ p5)) ∨ False))) ∧ (True → p2)) → p1) ∨ (p5 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68911212770569656005701168364 : ((p4 → (False ∨ ((p2 ∧ ((p1 → p5) ∨ ((((p4 ∧ ((True → (p3 ∨ True)) → True)) → p4) ∨ p4) ∧ False))) ∨ (False ∧ (p1 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172477420178091243422802559266 : (((((p5 ∧ p4) ∨ p1) → p2) → ((p2 ∧ p5) ∧ (((p3 ∧ p1) ∨ p5) ∨ p1))) ∨ ((p2 ∧ False) → ((p2 ∨ (p5 ∧ False)) ∨ (p2 ∨ False)))) := by
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
theorem thm_5_vars_219583716490460631983159078691 : ((True → (False ∧ (p4 ∨ True))) → (p4 ∧ ((((p4 ∨ True) ∨ True) ∧ (((p1 → ((p3 ∧ p5) ∨ (True → p1))) ∧ (p5 ∨ p1)) ∧ p4)) ∨ True))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714209548330940386309078925025 : ((((((False → p3) ∧ p2) ∧ (p5 ∨ True)) → (((((p3 → (p3 ∧ p5)) → p5) → (False ∧ p4)) ∧ (p4 ∧ (p5 ∧ (True → p1)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60637760264823673545171241640 : ((True ∧ ((((p4 ∧ p5) ∨ ((((p1 → p4) ∨ p5) → ((p1 ∧ p1) ∧ p2)) ∧ (p3 ∧ (False → p2)))) ∧ p3) ∨ (p3 ∨ (False → p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777350852813726231268301481072 : (((p1 ∨ ((False ∨ ((True → ((((p2 ∨ p3) → p4) ∧ ((p3 ∨ p5) ∨ p5)) ∨ (p1 → True))) ∨ p3)) ∨ ((p1 ∨ p3) ∧ (p4 ∧ p1)))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387559090089817679753867012012 : (((((p2 ∨ ((p2 ∧ ((True ∧ (p2 → (False → False))) ∨ p4)) → (p3 → (False ∨ (p2 → (p3 ∧ False)))))) ∨ (False → (False ∧ p4))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249186391670698861934144609491 : ((p4 ∨ p3) ∨ (((p1 → ((False ∨ (((((p1 ∧ p5) ∨ p5) ∧ (p1 ∨ p1)) ∧ p5) ∧ False)) ∧ p2)) → False) ∨ (p1 ∨ ((False → True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133986664125172018895408281174 : (((((((((((True ∨ p4) → True) → (p5 ∨ True)) ∧ (p3 → True)) ∨ p5) → False) ∨ p2) ∨ (p3 → True)) ∧ False) ∨ p5) ∨ ((True → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57294161567333203733665259339 : ((((p2 → p4) → p4) ∨ ((p5 → (True → (((p1 ∨ True) ∨ (((p2 ∨ p5) ∨ p5) ∨ (p5 ∧ ((True → p3) → p2)))) → False))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135962652870631550319069706036 : (((True ∨ (p4 ∨ ((p1 ∨ ((True ∧ False) ∨ p1)) ∧ p1))) ∧ (((p2 → p1) ∧ (p2 ∨ p2)) ∨ (p1 ∧ (p5 ∨ False)))) ∨ (p1 → (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115620029962333894655568996067 : (((p2 → ((False ∨ (p3 ∧ p3)) → False)) ∧ (((p1 ∨ (((False ∨ p3) → p2) → False)) → (p1 ∨ (p4 → p5))) ∨ (p2 ∨ p4))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681720483437403662478977849294 : ((((p5 → (True → (p5 ∨ (p4 ∨ ((True ∨ ((p4 ∧ ((p2 ∨ p2) → False)) ∧ (p3 → True))) ∧ p4))))) → (p2 ∧ (p1 ∧ (p4 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323492087822189331343378318148 : (p5 ∨ ((((p4 ∧ (p2 ∧ (((((False → (True ∧ p3)) → p5) ∨ p3) ∨ False) ∨ p5))) ∧ p5) ∨ (p2 → (p4 ∨ True))) ∨ (False → (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326973105559795250551947923930 : (True → (((((p1 → (p2 ∨ p2)) → ((p1 ∨ (True ∨ p2)) ∧ ((p4 ∨ True) → p1))) → ((True ∨ p1) ∧ False)) ∧ (p1 ∨ (p2 → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630754877994475998131179941325 : (((((p4 → (((p2 → (((((p4 ∨ p5) ∧ p4) → p5) ∨ (p4 ∧ (p5 ∧ p1))) ∨ p1)) ∧ ((p2 → False) ∨ p5)) ∨ False)) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715319760147589882888391195414 : ((((p4 → (((p5 ∨ False) → False) ∨ p2)) → (p3 ∧ ((p3 ∨ (((p3 ∧ (True ∨ True)) → p1) ∧ ((p4 ∧ (False → p1)) ∨ p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710039010468202822174781771016 : (((((p5 ∧ ((p4 ∧ False) → p1)) ∧ p4) ∧ ((p5 ∨ ((p3 → False) → ((p5 ∧ (False ∨ ((True ∧ p2) ∨ False))) ∧ p3))) ∧ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178468185023140348984081068787 : (((((((True → False) ∧ p5) → False) ∧ p5) ∧ p4) ∨ ((p2 ∧ p2) ∨ True)) ∨ ((p4 ∨ False) ∨ (p4 ∧ ((p2 ∨ (False → False)) ∧ (True ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586931353368080648068861702220 : (((((p2 ∨ ((((p2 → ((p3 → p2) ∨ (False ∨ (p4 ∨ (p1 ∧ p2))))) → (p3 → (p5 ∨ (p5 ∨ p3)))) → p2) ∧ p1)) ∧ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61881241960760537073335459575 : ((p2 ∧ (((p1 → p3) → (((p5 ∨ (((p5 ∨ False) ∧ (True ∨ (True → (p1 ∨ False)))) ∨ p2)) → (p2 ∨ p2)) ∨ False)) ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40027901490680276805335786944 : (((((((p1 → ((p3 → False) ∨ p4)) ∨ ((p2 ∨ ((p1 → p3) ∨ (p2 ∧ (p3 → (p5 → True))))) ∧ p2)) → p4) ∧ p5) ∧ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244085620703512178019347033889 : ((True ∧ p3) ∨ ((((p4 ∨ (p5 → (((p3 ∧ ((False → (p2 ∧ p3)) → p5)) ∧ p5) ∧ p1))) ∧ p3) ∨ p3) → ((p5 → False) ∨ (p4 → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198412747006126317820681332931 : ((p4 ∧ (((p2 ∨ p1) ∨ (p2 → False)) → p5)) ∨ (((((True ∨ True) ∨ p2) → p3) ∧ ((p1 ∧ p2) ∨ (False ∧ True))) ∨ (True ∨ (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59669768657515730467571575933 : (((True ∧ p1) → (True → ((True ∧ (((p2 ∨ (p2 ∨ p4)) ∨ p4) ∧ (True ∨ (p5 → p2)))) ∧ (((p5 ∨ False) ∨ False) ∧ (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346582546568715668511323696327 : (p3 → (((((p1 → (False ∨ False)) ∨ (p2 ∧ (p5 → (((p1 ∧ True) ∨ p1) → ((p3 ∧ p2) ∨ p2))))) ∧ p3) ∧ p5) ∨ ((p3 ∧ p4) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354912950830830686452541271818 : (p5 → ((False ∨ (((True → p3) → (p2 ∨ p1)) ∨ (p2 ∨ (((p5 ∨ True) ∨ (False → p3)) ∧ ((p1 ∨ (p4 ∨ (p3 → p5))) → False))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158650175395678633502728898887 : ((p1 ∧ (((True ∧ p1) → p2) ∧ (p5 → ((p3 ∧ ((p2 ∧ p5) ∨ ((p2 ∧ p1) → p2))) → False)))) ∨ (p1 → (False ∨ (True → (True ∧ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180867111034131880139551043673 : (((p2 ∨ (p5 → p5)) ∨ (True → (p1 ∨ ((p1 → (p5 → False)) ∧ p2)))) → ((False ∧ ((p2 ∨ p4) → p2)) ∨ ((True ∨ p3) → (False ∨ True)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
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
theorem thm_5_vars_608933454689784350405806063355 : (((((((p2 ∨ p3) → ((True ∨ (p2 → False)) → (((p5 → p1) → p3) ∧ p4))) → (p5 ∧ ((p1 ∧ p4) ∧ (True ∧ True)))) ∨ p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165966726683197873762754160974 : (((p1 → p4) ∧ (p5 ∧ (((p4 → p3) ∧ False) ∨ ((p4 → p3) ∧ (p4 ∧ (p3 ∧ False)))))) ∨ (p2 → ((p1 ∧ p4) → (p4 ∨ (p1 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53849220123749781357242111323 : (((((p2 ∨ False) ∧ p1) ∧ (p3 ∨ (p4 ∧ (p2 ∧ p3)))) ∨ (((p2 ∧ p5) ∨ (p3 ∨ (False → ((p4 ∧ False) ∧ p3)))) ∨ (p1 ∧ p1))) ∨ p1) := by
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
theorem thm_5_vars_305578370602819329052426407136 : (p1 ∨ (((False ∨ (((p1 ∨ (p5 → (p1 ∨ p1))) ∧ False) → True)) ∧ p5) ∨ (((p5 ∨ p1) ∧ p3) ∨ ((p4 ∨ ((p4 ∨ p2) → True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_906204800007248833959987789691 : ((((((((p4 ∧ ((((p3 → ((p3 ∨ True) → p5)) ∨ p3) → p5) ∧ p5)) → p1) ∨ p5) ∨ True) ∨ False) → ((p1 ∧ (p3 ∧ p4)) ∧ p4)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ ((((p3 → ((p3 ∨ True) → p5)) ∨ p3) → p5) ∧ p5)) → p1) ∨ p5) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168147782746843306036875486371 : ((((True ∧ p2) ∧ p3) ∧ (((p4 ∧ p2) ∨ p2) ∧ (((p3 ∧ p1) ∧ False) → (p2 → p1)))) → (((p5 ∨ p5) ∨ (p4 ∧ p4)) ∨ (p3 → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314485522575033746427174057605 : (p3 ∨ ((False ∨ (p5 ∧ (p4 ∨ ((p5 ∧ ((True ∨ (p2 ∨ ((False → True) ∨ True))) ∧ p3)) ∧ (p3 ∧ p3))))) → ((p2 ∧ False) ∨ (p5 ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
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
        -- Conjunctions on the left can always be decomposed.
        let h15 := h9.left
        let h16 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h9.left
          let h20 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h9.left
            let h24 := h9.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h9.left
            let h27 := h9.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165980626387495952369138855507 : (((True ∧ False) ∨ ((((True → (p5 ∨ (True → (True ∧ p1)))) → p2) → True) → (p4 ∨ False))) ∨ (p2 → ((p5 ∧ p2) ∨ ((p5 ∧ p3) → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41529866897871186652156590475 : ((((p3 → (p2 ∨ ((p5 ∨ p5) ∧ (True ∨ (p2 → p2))))) ∧ ((((p3 ∨ True) ∨ ((p5 ∨ False) ∧ True)) ∧ (p4 ∨ p5)) ∧ p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677907046247651661279106960888 : (((((True ∧ (p1 → ((False → (((p4 ∧ p3) ∧ (p4 → p1)) ∨ (True ∧ p3))) → False))) ∨ (True ∨ False)) ∨ ((p3 ∧ (p4 → p1)) ∨ p5)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330589096083930404664985351140 : (True → (p5 ∨ (p2 → ((((p3 → False) ∨ ((p3 → (((p4 ∧ (True ∧ (False ∧ p3))) ∧ ((p5 ∨ p4) ∧ False)) ∧ p4)) ∨ True)) ∧ p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150226339823337281630272359916 : ((p2 → (p3 ∨ ((False ∧ ((p3 ∧ (p1 ∧ (True ∨ p4))) → (p5 ∨ p2))) ∨ (p1 ∨ ((p1 ∨ True) ∨ True))))) ∨ ((p1 ∧ True) → (p4 ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60014178413549439685783195607 : (((p1 ∨ False) → ((False ∧ (((p1 ∧ ((((p4 ∧ p5) ∨ p3) ∧ (p3 ∨ (p2 ∨ True))) ∨ (True ∧ (p4 ∨ p3)))) ∨ p3) ∧ p4)) ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7325723152057507223981982447 : (((p4 ∨ (((p3 ∨ (((p1 ∧ False) ∧ p1) ∨ p1)) ∧ (p2 ∨ False)) ∨ (True ∨ (False ∧ (((p3 → (False ∧ p4)) ∧ p5) ∧ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41498402254098952350430343360 : (((((p1 → ((p5 ∨ (True ∧ False)) ∧ p5)) → ((p4 ∨ p3) ∧ p3)) → ((p4 ∨ ((p1 ∨ p4) → (p4 ∨ (p1 ∧ p3)))) ∨ True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39278378539993851503412646710 : (((p1 ∧ ((((True ∨ (p5 ∧ p4)) ∨ (True ∨ (True ∧ ((p4 ∧ (True ∨ (p3 ∨ (p1 ∨ (False ∨ p3))))) ∨ p4)))) → p5) ∨ False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152307124528082355256391406474 : (((((True → p4) ∧ False) ∨ p4) ∧ ((p5 ∨ p2) ∧ (p3 → (((p4 ∨ p4) ∧ ((p1 ∧ p4) ∨ False)) ∨ p2)))) → ((p3 → p2) ∨ (True → p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114462026755110306517915430130 : ((((((p3 → ((p5 ∧ p5) ∨ p3)) ∨ (p1 → (False ∨ p5))) ∨ (p2 ∧ (p4 ∧ True))) ∨ p3) → (p2 ∨ (True → (p4 ∧ False)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263483795339626165775404832067 : (True ∧ ((p2 ∧ ((((p2 ∨ p1) → p3) → (((False ∨ (p1 → ((p4 → (p1 → p1)) ∧ p4))) → p5) → p5)) → p4)) → (p3 ∨ (p2 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592425473589128231920809649883 : ((((((p5 ∨ (True ∧ ((p2 ∧ (p1 ∨ False)) → p3))) ∧ (((True → p4) ∨ (p2 → ((p2 ∧ True) → p1))) ∧ p1)) → (p3 ∨ p4)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354415950127259731650852196129 : (p5 → (((p2 → p5) ∧ ((p1 → (p2 ∧ p4)) ∨ (((p4 → ((False ∧ p3) ∨ (p4 ∧ (False ∧ p3)))) ∧ (p3 → (p3 ∧ p4))) ∨ p5))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45460032423862906165599359545 : (((True ∨ (p3 → (((p1 → (True → (p4 ∨ (p5 → p4)))) ∨ ((((((True → p3) ∧ False) → False) ∧ p4) → p1) → False)) → False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337144676080119178368190530421 : (p1 → ((p1 → (((p2 ∧ ((((False ∨ p4) ∧ (p1 → p4)) → p4) ∧ False)) ∧ (False ∧ p2)) ∨ ((p4 ∧ True) → (p5 → p2)))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4176359146456922104886444322 : (p4 ∨ (((p4 ∨ p2) ∧ p2) → ((False ∧ (p1 ∧ ((p3 ∨ p4) → (False ∨ (((p1 → (p4 ∨ False)) → (p4 ∧ False)) ∨ p4))))) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762802530613647956846786960735 : (((p3 ∧ ((((True ∧ ((p4 ∨ False) ∧ p4)) ∨ False) ∨ p2) ∨ (p5 ∧ ((p3 ∨ (((p4 ∧ p2) → ((True → p1) ∧ p5)) ∨ p3)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161717791400774860916099776970 : ((p3 ∨ ((((p3 → True) ∨ p5) ∨ (p2 ∧ (False → ((p1 → (False → (p4 → p2))) → False)))) ∨ p5)) → (p1 ∨ ((p1 → p1) ∨ (True ∨ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185018195962967694870012550428 : (((p2 ∨ p1) ∧ (p5 ∨ ((p2 ∧ (False → p1)) → (p4 ∨ p2)))) ∨ (p5 ∨ (((((p4 ∨ p1) → (True ∨ p2)) ∧ p2) → (p4 ∨ True)) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592500783886929840959521507918 : ((((((False ∨ p1) ∧ ((False → ((((p3 → True) ∨ p2) ∨ p5) ∧ (False ∨ (((p5 ∧ False) ∧ p2) ∧ True)))) ∨ p1)) → (p5 ∧ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137114946333497228669261576842 : ((True ∧ ((p2 ∧ ((p5 ∨ False) ∧ ((p5 ∧ p3) ∧ p3))) ∨ (True → (p1 ∧ ((True ∨ p5) → ((False ∨ False) → p5)))))) ∨ ((False ∨ False) → p2)) := by
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
theorem thm_5_vars_307496644513041383056816634524 : (p1 ∨ (True → ((p2 ∧ ((p3 ∨ p5) ∨ (((p2 ∨ (p2 → p3)) ∧ (((True ∧ p2) ∨ p1) → (True ∨ p3))) ∧ (p3 ∧ p5)))) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_112546690769036459527324634725 : ((((((p5 ∧ p4) → (p2 ∧ p3)) ∧ (p3 ∧ (((((p4 ∨ p4) ∨ (False ∨ p5)) ∧ (False → p4)) → p3) → p5))) → p4) → p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166501281178532320866214053615 : ((p3 ∨ (p1 → (p3 ∨ (((p2 ∧ p1) → p3) ∧ (False ∧ (p1 → (p5 ∨ (True ∧ p5)))))))) ∨ (True ∨ (p5 ∨ ((True → p5) ∧ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258191662995744560392825436735 : ((p4 ∨ p4) → ((True ∧ p5) → (((((p2 → False) ∨ p5) → False) ∨ False) → ((False ∧ (p3 ∨ ((False ∧ p5) ∨ p1))) ∧ (p1 ∧ (False ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h18 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h19 := h14 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h21 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h22 := h14 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h2.left
    let h26 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h27 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h28 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h29 := h24 h28
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h31 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h32 := h24 h31
      -- False on the left can always be used.
      apply False.elim h32
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h2.left
    let h36 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h37 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h38 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h39 := h34 h38
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h41 : ((p2 → False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h42 := h34 h41
      -- False on the left can always be used.
      apply False.elim h42
  case inr h43 =>
    -- False on the left can always be used.
    apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655245457779898938255189597753 : ((((((p4 ∨ (((p2 ∧ p2) ∧ p3) ∧ (((p5 ∨ p3) ∧ (p4 ∨ p2)) → True))) → ((p3 ∧ p2) ∨ p1)) ∧ (p3 → p5)) ∨ (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134519306852501733700414110436 : ((((True → (False ∨ ((True ∧ True) → ((((p4 ∨ p4) ∨ p4) ∧ (True ∨ p1)) → ((False ∨ p2) ∧ p3))))) ∨ p2) → p5) ∨ (p2 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186786934674274588866771965238 : (((((True ∧ p3) → p1) ∨ p4) ∧ (True ∧ ((p5 ∨ p1) → p2))) → (((p4 ∨ (p3 ∧ (p1 ∨ False))) ∧ (False ∨ p2)) → ((p5 ∨ False) ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h9.left
        let h15 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h23.left
          let h29 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233899034190152331476082793528 : ((p4 ∨ (p4 ∨ p4)) → (((False → (p5 ∧ p5)) ∨ p2) → ((p2 ∧ (p3 ∧ p2)) ∨ ((((p2 → p4) ∧ False) ∨ True) ∨ (False → (p2 ∧ p5)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_433999388013581660302842628959 : ((((((p4 → (((((((p4 ∧ p4) ∧ p3) ∧ p4) ∧ p1) → (True ∨ (p2 → False))) → (p3 ∧ False)) ∨ p4)) ∨ p4) → False) → (p1 → p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (((((((p4 ∧ p4) ∧ p3) ∧ p4) ∧ p1) → (True ∨ (p2 → False))) → (p3 ∧ False)) ∨ p4)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111828928680697129802053635776 : ((((p3 ∧ (((p5 ∧ (p4 ∨ (False ∨ p3))) ∨ True) → (p1 → (p2 ∨ ((True → p3) ∧ p3))))) ∧ ((p5 → p3) ∨ p1)) ∨ p2) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624578947199414917873626763258 : ((((p4 ∨ (((p1 ∧ (True → False)) → (((p1 ∨ p4) ∧ p1) ∨ (False ∧ (p1 → (False ∨ p2))))) ∧ ((p2 ∨ p5) ∨ (p1 → p5)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169048582111171580212194764643 : ((p2 → (p4 ∨ ((p1 ∧ ((p3 ∨ ((False → False) ∧ (p1 → p4))) → (p2 → True))) ∧ p3))) → ((p4 → (p5 ∧ p1)) ∨ ((p2 → True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149455134165375705674783225680 : ((False ∧ ((True ∨ (p3 ∨ (((p1 ∧ (((p5 ∧ (p5 ∧ True)) → p2) ∧ p2)) ∧ p3) → True))) → (True → p5))) ∨ (p5 → ((p1 ∧ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98483756819192115593269854022 : ((p5 ∨ ((p2 → ((((p3 → (((((p4 ∧ True) ∧ False) ∧ p3) → (True → ((p1 → p2) ∧ p3))) → p4)) ∧ p5) ∧ p4) ∨ True)) → p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → ((((p3 → (((((p4 ∧ True) ∧ False) ∧ p3) → (True → ((p1 → p2) ∧ p3))) → p4)) ∧ p5) ∧ p4) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165501356375813670961790089609 : (((p5 ∨ (p3 → ((p4 ∧ (p5 ∨ p2)) ∧ (False ∧ False)))) ∨ ((p3 → p4) ∨ (True ∨ p2))) ∨ (p1 → ((p3 ∧ (True ∨ (p1 ∧ p5))) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113717332983592229154894800242 : ((((((True ∧ (p4 ∧ (p4 ∨ p3))) ∨ (False ∧ ((False ∧ ((p5 → False) ∨ p1)) ∨ p1))) ∨ p4) → (True ∧ p3)) → (False ∨ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123181041514091880510136308637 : (((p1 → (((((p2 ∨ p4) ∨ ((p1 ∨ p5) ∧ (p3 → p5))) ∧ p4) ∧ (p3 ∨ (p4 ∨ p2))) ∨ p1)) → ((False ∧ True) ∧ p5)) → (p3 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((((p2 ∨ p4) ∨ ((p1 ∨ p5) ∧ (p3 → p5))) ∧ p4) ∧ (p3 ∨ (p4 ∨ p2))) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822553604173718645470599933352 : ((((((p1 → (p1 → (((p4 ∨ p4) → p2) → p4))) ∨ True) → ((p2 ∧ (True → False)) ∧ ((((p2 → True) → p1) ∧ p3) ∨ p2))) ∧ True) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → (p1 → (((p4 ∨ p4) → p2) → p4))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158678753454379536110399564924 : ((p2 ∧ ((p2 → (((p4 ∨ (p3 ∧ (False ∨ (p4 ∧ p1)))) ∧ (False ∧ p3)) ∧ p5)) ∨ (p2 ∨ p3))) ∨ (p5 → (False → ((True ∨ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



