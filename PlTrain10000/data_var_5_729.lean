variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346684178111958515339876054851 : (p3 → ((((False → True) → (p2 ∨ (False → p4))) ∨ ((p3 → ((p2 ∧ p3) ∨ (((p3 → p1) ∧ p2) → p5))) ∨ p3)) → (p1 → (p4 ∨ True)))) := by
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
theorem thm_5_vars_649585102469931855367407471078 : ((((((((p2 → (p4 → (False ∨ p1))) → p4) ∨ ((True ∧ False) ∧ (((p3 → False) ∧ p2) → p4))) → p3) ∨ (p1 → p1)) ∧ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63452540961488553968713660418 : ((p5 ∧ (p5 → (((p2 ∨ (p2 ∧ (((p2 → (p3 ∨ p2)) → False) ∨ p5))) ∧ (True → (p2 ∨ True))) → ((p1 ∨ p5) ∧ (p4 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160880951107299149045188384060 : ((((p1 ∨ (False → p4)) ∨ False) ∨ (((p3 ∧ (p2 ∧ p5)) → (p4 ∧ (p4 ∧ p3))) ∨ (True → False))) → (p4 → ((p5 → False) ∨ (True ∧ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200661068281915935242533411188 : ((p1 ∧ ((p4 → (p3 ∨ False)) ∨ (p4 ∧ False))) → ((True → (False ∧ False)) → ((p5 ∧ (p5 → ((True → (p3 → False)) → p3))) ∨ (False ∨ p5)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115651665635334669796885930801 : ((((p5 → ((False ∨ p5) → True)) → False) ∨ ((p4 → p4) ∧ (p4 ∨ (((p4 → p2) → (((p4 ∧ p5) → p5) ∧ p2)) ∨ p3)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47535747558751516528815732962 : (((p4 ∨ (p3 ∧ ((((((p5 ∧ p4) → p1) → (p2 ∧ True)) ∨ ((False ∧ p4) ∨ False)) ∧ p3) ∨ ((p2 ∨ p3) ∧ p5)))) ∨ (p3 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114680938163521785515880996734 : (((False ∨ ((False ∧ (((p5 ∧ p4) ∧ p2) ∨ p4)) ∧ (((p4 ∧ p2) ∧ p1) ∨ p3))) ∨ ((False ∧ ((p5 ∨ True) ∧ p3)) ∧ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207597862717444293721279118998 : (((((False ∧ p3) ∨ True) → p4) → p5) → (((False → (p5 ∨ p2)) ∨ False) ∧ (((((p2 → p3) ∨ False) → p2) → p1) ∨ (p4 ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317582591885199196702996782086 : (p4 ∨ (((((((True ∧ False) ∨ (p1 → True)) ∨ p1) ∧ (((p2 ∧ False) ∨ (p3 → (False ∧ (p2 → p4)))) ∧ (p2 ∧ p5))) → False) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150461382440524071446298542388 : ((((p2 ∨ ((((((p2 ∨ p1) ∨ ((True → p1) → p4)) → True) ∧ (p3 ∨ p3)) ∨ p2) → p4)) → False) ∧ p1) → ((p1 → (False ∨ p5)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46162041493692976639185511813 : (((((((p5 → False) ∧ ((p2 ∨ p2) ∧ (False ∨ p4))) ∨ (True → False)) ∧ ((True ∧ True) → ((True → False) ∨ p3))) → p5) ∧ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164899775528067532967408532460 : (((((((((p2 → p1) ∨ p2) ∨ True) → ((p4 ∨ True) ∨ p5)) ∨ False) → p2) ∧ True) → p4) ∨ ((True → (True ∧ ((p2 → p5) ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191796941038019891887482927407 : ((p2 ∨ ((p1 ∧ ((p1 ∨ (True ∧ False)) ∨ p5)) ∨ p2)) ∨ (((p1 → True) ∨ (True ∨ (p3 ∧ p5))) ∨ (p1 ∧ (((p4 ∨ p4) ∧ p1) ∧ p5)))) := by
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
theorem thm_5_vars_135163463295089243854675502163 : ((((((p2 → p3) ∧ (((p3 → (p5 → False)) ∧ p4) → (p1 ∨ (True ∨ (False ∨ p3))))) → p1) ∧ p4) → (p3 → p2)) ∨ (True ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299436282543620497503953326042 : (False ∨ ((False ∨ ((False → (p5 ∧ ((p3 ∨ p3) → p3))) → ((p3 ∧ (((((True → True) ∨ p2) ∨ p1) → p2) ∧ (p5 ∨ False))) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180319638850210003969313039215 : ((((p2 → (p3 ∨ p2)) ∧ ((p4 → (p1 ∨ p5)) ∧ p4)) ∧ (p5 ∨ False)) → ((p4 → ((True ∧ p2) ∧ ((p5 ∧ p4) ∧ p3))) ∨ (True ∧ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616502615678367850120919814822 : (((((False ∨ (((((p2 ∧ True) ∧ (p2 ∨ True)) → True) ∨ p5) ∨ p1)) → (p5 ∨ (((p5 → (p1 ∧ p3)) ∧ p4) ∧ (p1 ∧ p3)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_323523971669658797279072262985 : (p5 ∨ ((p2 ∨ (p2 ∧ (p2 ∨ (((True → p3) → p5) ∧ ((((p2 → False) ∨ (p2 → True)) → p5) → (p1 ∧ True)))))) ∨ (p4 → (p3 → True)))) := by
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
theorem thm_5_vars_803454226782945874591294461531 : (((p3 → ((((True ∧ (p5 ∧ False)) → (p5 ∨ (((((p4 → p5) ∨ p1) ∧ p3) ∧ ((p5 ∨ p4) ∧ True)) ∧ (p2 ∨ p1)))) ∧ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354699488156713522345914816530 : (p5 → ((((((p4 ∨ False) ∧ p1) → (p3 ∨ (((False → (False ∨ (p3 → (p5 ∧ p4)))) → p3) ∧ (True ∧ False)))) ∨ True) → (p5 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165146047834016699349203274368 : ((((p3 ∨ ((p3 ∧ ((True → p1) ∧ (p4 ∧ p1))) ∨ p2)) ∨ (True → p3)) ∧ (p3 ∨ p5)) ∨ (p1 ∨ (((False ∧ (False ∨ p5)) → p4) ∨ p5))) := by
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
theorem thm_5_vars_789399969470874436051338779741 : (((p5 ∨ (((p3 ∨ (p4 ∨ (False → p5))) ∧ ((p1 → True) ∧ (False ∨ (p4 ∧ False)))) ∨ (p3 → (False → (p4 ∨ ((p3 ∨ p5) ∧ p2)))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137161114661129020006148508513 : ((False ∧ (((p5 ∧ (((((p3 ∨ False) ∨ p5) → p5) ∧ ((p1 → p5) ∨ (p2 ∧ (p3 → p5)))) ∧ p2)) → p2) → p3)) ∨ (True ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175013367684705949363436083332 : ((p1 ∧ (((p4 → (p1 ∨ (((p2 → p3) ∨ (p1 ∨ p2)) → p3))) ∨ p4) → True)) → ((p1 ∧ (p1 → ((False → p3) ∧ p3))) → (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200447876363209003287173784274 : (((True → p3) ∨ (p4 ∧ (p4 → (p5 → False)))) → (p2 → (((((p1 ∧ False) → p2) ∨ (p2 ∨ ((p2 ∨ False) ∨ p4))) ∧ True) → (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55854763597101342163468474303 : (((p3 ∧ (True ∧ (p3 → p4))) ∧ (((((p3 ∨ True) ∨ True) ∧ p5) → ((p3 → (p2 → (p4 → p2))) ∨ ((p3 ∧ False) → True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197402767972045912798627412251 : (((True → (p1 → (True ∨ (True ∨ p5)))) → p1) ∨ (((p3 ∨ (p1 ∧ p1)) ∨ (p1 ∨ ((p2 ∨ p4) ∨ ((p3 ∨ (True ∧ True)) → p2)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90521976649648532733323016310 : (((p3 ∧ True) ∧ ((p1 ∨ ((((True → p2) → True) ∨ True) ∨ p2)) → ((((((p4 ∧ (p3 ∨ p2)) → p3) ∧ p1) ∧ False) → p5) ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ ((((True → p2) → True) ∨ True) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46324348194493406538060650356 : ((((p4 ∨ (((p5 ∨ p2) ∨ ((p4 ∧ True) ∨ ((p4 → (p2 ∨ False)) ∧ True))) → False)) ∨ (p5 ∧ ((p1 → p5) ∨ False))) ∧ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159795584832429274948314607477 : (((p1 ∧ (((True ∧ True) → p3) → ((p1 ∧ (p1 ∧ p4)) ∨ (p5 → (p3 ∨ (False → p1)))))) ∨ p2) → (p2 ∨ (((True ∨ p5) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228459683864131940002276264735 : ((False ∨ (p3 ∨ p2)) ∨ ((p5 ∧ (((p5 ∧ ((p5 → p3) ∨ ((((p4 ∨ (p2 → p1)) → True) → p2) ∨ p4))) → p5) ∨ p3)) → (p1 ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352225044816551911378737485366 : (p4 → ((((True ∨ p3) ∨ p3) → p5) ∨ ((False ∨ ((((p2 ∨ p4) ∧ p3) ∨ (p1 ∨ True)) → (False ∨ p1))) → (True → ((p1 ∧ p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 ∨ p4) ∧ p3) ∨ (p1 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44586881037082779835937812308 : ((((p3 ∧ (((p2 → True) → (False → p3)) ∧ p2)) ∨ ((((((p4 ∧ p5) ∧ (p5 → (p3 ∨ p5))) ∨ p3) ∨ p3) → p1) ∧ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59375878820834832505991204498 : (((p5 ∨ p5) ∨ ((p4 ∧ p4) ∧ (((((False ∨ False) ∧ (p2 ∧ False)) ∨ p1) → ((p1 ∧ False) ∧ p1)) ∧ (p3 ∨ ((True ∨ p5) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207709625842130963229278972092 : (((False ∧ (False ∨ (p3 ∧ p5))) → p2) → (((((p1 ∧ (p5 ∧ p5)) → (p5 ∨ p4)) → (p3 ∨ ((p2 ∧ (p2 → p5)) → False))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258427619926504609167891767483 : ((p5 ∨ p1) → ((((True ∧ p5) → True) → False) ∨ (((p4 → (False ∨ ((p1 ∨ p4) → ((True → True) ∨ p3)))) ∧ False) → ((True → p1) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66018384611278756985815278610 : ((p5 ∨ (((p1 → ((((True ∧ (False → p1)) ∨ ((False ∧ p4) ∨ p3)) ∧ (p2 → False)) ∨ (p4 → (False ∨ p4)))) ∧ (p1 ∧ p3)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308618076659612254800328756161 : (p2 ∨ (((p3 ∨ False) ∨ ((False ∨ (p2 ∨ (p3 ∨ (p5 ∨ p5)))) ∧ ((True ∧ p4) ∧ ((p2 → ((p1 ∧ True) → False)) ∨ (p5 → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616790183824251033044348803931 : (((((p4 ∧ ((True ∨ p4) → ((p3 → p2) ∨ (p1 ∨ False)))) ∨ (True ∨ (((True ∨ p2) → (((False → p5) ∨ False) ∨ p1)) ∨ p3))) ∨ p1) ∨ False) ∧ True) := by
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
theorem thm_5_vars_116786527771436070992571940921 : (((p1 ∨ p3) ∨ ((p4 ∨ (p2 ∧ (((((((p1 ∨ p3) ∧ p4) ∧ p1) ∧ True) ∨ p5) ∧ False) ∨ p5))) ∨ (p1 → (p3 ∧ p1)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228940045301324866925155354428 : ((p4 ∨ (p4 ∨ p5)) ∨ ((((True → False) ∧ (p4 ∧ (p2 ∧ (p5 ∧ (p5 ∨ (((p5 ∧ p4) ∨ p1) ∨ (p4 ∧ p3))))))) ∨ False) → (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h33 := h23 h32
      -- False on the left can always be used.
      apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h39 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h40 := h23 h39
          -- False on the left can always be used.
          apply False.elim h40
        case inr h41 =>
          -- One of the premise coincides with the conclusion.
          exact h41
      case inr h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h46 := h23 h45
        -- False on the left can always be used.
        apply False.elim h46
  case inr h47 =>
    -- False on the left can always be used.
    apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41693880036358924814504670644 : (((((((p3 → p5) → p2) → p1) ∨ False) → ((p1 → (((p5 ∨ p5) ∧ False) ∨ (((p4 ∧ True) ∧ True) → (False ∧ False)))) ∧ p4)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338071877445859337940258169961 : (p1 → ((((p3 ∨ p2) → p1) ∨ ((p4 ∨ True) → (p1 ∨ p2))) → (p5 → (p3 ∨ (p4 ∨ ((p2 ∨ p1) ∧ (((p1 ∨ p4) ∨ True) ∧ p1))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167598509033446156978386682820 : (((False ∨ ((True ∧ ((p5 ∨ (p4 ∧ p4)) ∨ (p2 → p2))) ∨ (p3 → p4))) ∨ (p3 ∧ p4)) → ((p1 ∧ p4) → (((p4 ∧ p5) ∨ p5) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134497724768712404906111361401 : ((((((p5 ∧ (p5 → (((p1 → True) ∧ p1) ∧ p4))) ∧ (True ∧ p4)) ∧ (((True ∧ p4) → p1) ∧ p2)) ∨ p3) → False) ∨ ((p5 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217774607238919955732908159767 : (((True ∨ (False ∧ p3)) → p3) → ((((p3 → (p5 → ((((True ∨ p3) ∨ p5) → ((p2 ∧ (p2 ∧ p4)) ∨ False)) ∧ p2))) → p1) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157602998299230594606970274208 : (((p5 → (((True → p4) ∧ ((p3 → False) ∧ (p2 ∨ p3))) → (False → (p3 ∨ p5)))) → (True ∧ p4)) ∨ (True ∨ (p5 → ((p4 ∧ p3) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95623193102922353176726565831 : ((p5 ∧ (((((p1 ∧ p3) ∨ True) → p4) ∧ True) ∧ (((p1 ∧ ((False ∧ True) ∧ (True ∧ ((p2 → p1) → p1)))) ∨ p5) ∨ (p5 ∨ p3)))) → p4) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : ((p1 ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : ((p1 ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h24 : ((p1 ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h25 := h6 h24
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135584561211108526729002175752 : ((((p2 ∨ ((p1 ∧ (((p1 ∧ (True ∧ p5)) ∧ p1) ∧ (p1 ∨ p2))) → p3)) → p2) ∨ ((p1 → (p3 → p4)) ∨ p3)) ∨ ((p1 ∧ p2) → p2)) := by
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
theorem thm_5_vars_20234643405392441281257735867 : (((((p5 → p1) ∧ ((p4 → p5) → p1)) ∧ (p3 ∨ (p5 → (False ∧ False)))) ∨ ((p2 ∨ (p2 ∧ (p3 ∧ ((p4 ∧ False) → p4)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_129428055273868752756627448775 : (((p5 ∨ ((True → ((p3 ∨ (p2 → (p1 → (False → (True ∧ True))))) → ((p5 ∧ (p4 ∧ False)) ∧ p1))) → p1)) ∨ p3) ∧ (p2 ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (p2 → (p1 → (False → (True ∧ True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h12
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259734760219676301253421708064 : ((p1 → p2) → ((((p2 → (p4 ∨ p1)) → (p2 ∧ (((p1 ∨ (False ∨ p4)) ∧ p1) → (((p4 ∨ p3) ∨ p3) ∧ (p5 ∧ p4))))) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352413832211454447074942356514 : (p4 → ((p5 ∧ (True ∨ p4)) ∨ ((((False ∧ (p2 ∨ True)) → (True → p4)) → (p1 ∨ p2)) ∨ ((((p3 ∧ p4) ∧ p5) ∧ (p4 ∧ False)) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256485068358577614994343910219 : ((False ∨ p4) → (((p2 ∨ p5) → (p5 ∧ p5)) → ((((p3 ∧ (((False ∧ True) ∨ False) ∧ False)) ∨ (p5 ∧ (False → (True ∧ p4)))) → p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162450291472763174918326374331 : (((((p2 ∨ p1) ∨ p2) → ((p3 ∨ p4) ∨ (p4 ∧ (((False ∨ False) ∧ False) ∧ p1)))) ∨ True) ∧ (False → (((p4 ∨ p1) → (p2 ∨ p3)) ∧ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655242457892986438025711177094 : (((((((p4 → p2) ∨ ((p5 → (False ∨ ((True ∨ (True ∨ False)) → p4))) ∧ p2)) ∨ ((p1 ∨ False) → p1)) ∧ (p4 → p2)) ∨ (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113195099967438298984484721614 : ((((p5 ∨ ((p4 → ((p1 ∧ ((p3 ∧ p3) ∧ (((p5 ∨ (p2 ∨ p2)) ∧ p5) → False))) ∨ False)) ∧ p2)) ∧ False) ∧ (p4 → p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158581155774057906914824067732 : ((True ∧ (False ∧ ((p2 ∨ p1) ∨ ((p5 → p3) ∨ (False ∧ ((p4 → True) → ((p2 ∨ False) ∨ True))))))) ∨ (p1 → ((True ∨ (p3 ∨ p5)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151995909268741843452340345878 : ((((p5 ∨ (((False ∨ p2) ∨ p1) ∨ (p3 ∨ p4))) → (True ∨ True)) → ((p5 ∨ (False ∨ p5)) ∧ (p4 ∧ p2))) → (((p3 ∧ p5) ∨ p4) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (((False ∨ p2) ∨ p1) ∨ (p3 ∨ p4))) → (True ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- False on the left can always be used.
            apply False.elim h8
          case inr h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : ((p5 ∨ (((False ∨ p2) ∨ p1) ∨ (p3 ∨ p4))) → (True ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h25 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h29 := h1 h17
  -- We need to get the right conjuct of h29 based on <expert-advice>.
  let h30 := h29.right
  -- We need to get the left conjuct of h30 based on <expert-advice>.
  let h31 := h30.left
  -- One of the premise coincides with the conclusion.
  exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764080116704268194285825857466 : (((p3 ∧ (p2 → (p5 ∨ (((((p4 ∧ p2) ∨ ((p3 → p2) ∨ (p4 ∧ p2))) → p3) → (p4 ∧ p3)) ∨ (((True → p4) → p5) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198903375491959489790921574754 : ((p3 → (((p1 ∨ p1) → p5) ∨ (p2 ∨ p5))) ∨ (p4 ∨ (((p5 ∨ p3) → p4) ∨ (((p3 → True) ∧ (True ∨ (p3 ∨ (False ∨ p2)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113836196729869092773127907248 : (((p2 ∨ ((((True ∧ p1) → True) ∨ ((False ∨ ((p2 ∧ (p4 → False)) ∨ ((True ∧ p4) ∧ p3))) → p5)) ∨ True)) → (p2 ∧ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238070372742761355593498826544 : ((True ∨ p2) ∧ ((((False → (((p2 ∨ ((p4 → p3) → (((p2 → p1) ∨ True) ∨ True))) ∧ p5) → p3)) → p3) ∨ True) ∨ ((p4 → p4) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120002927354848113248072492973 : (((((True ∨ ((p5 ∧ (p1 → p4)) → True)) → (p4 ∨ (p1 ∧ (True → p2)))) → ((p3 ∧ p5) ∨ (True → (True → p5)))) ∧ p4) → (True → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∨ ((p5 ∧ (p1 → p4)) → True)) → (p4 ∨ (p1 ∧ (True → p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709173796629954667494453814284 : (((((p2 ∧ p4) ∧ (p4 → ((True ∨ p2) ∨ True))) → ((p4 ∧ (False ∨ ((p5 → (p5 ∨ ((False ∧ p1) ∧ p5))) ∧ (p3 → p5)))) ∨ True)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262380559802486002521848530039 : (True ∧ (((p3 → p4) ∧ ((p4 ∨ ((p5 ∧ True) ∧ p4)) ∨ (p2 ∨ ((p3 ∨ p4) → ((((p4 ∨ p2) ∧ p4) ∨ p1) ∧ (p2 → p3)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617896346059134296673755571209 : ((((((p2 → p1) ∨ ((p4 ∨ True) ∧ p2)) → ((((((p5 → p3) ∨ False) ∨ ((p5 ∨ False) → (p2 → p4))) ∧ True) ∨ p2) ∨ p2)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47068917662978338700532822565 : ((((False ∧ ((((((False ∧ (p1 ∧ False)) ∧ True) ∧ p1) ∨ p4) ∨ ((p3 ∨ p3) ∨ (p5 → True))) ∧ False)) ∨ (True → True)) ∨ (False ∧ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3358538565675679438894905501 : ((p3 ∨ p5) → (p1 ∨ ((p3 ∧ p3) → ((((p1 ∧ p2) → p2) ∧ (((p3 ∨ True) → (p5 ∧ True)) → (p2 → (p4 ∨ False)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147563529472688021606992520116 : (((((p2 ∨ (((False ∧ True) ∨ p3) → (((False ∧ False) → p3) ∧ ((True → False) ∧ False)))) → p1) ∧ p3) → p2) ∨ ((False ∧ (p2 → False)) → p2)) := by
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
theorem thm_5_vars_259033262086241270490803491693 : ((True → p4) → ((((p5 ∧ False) ∧ False) ∨ (p2 → p5)) ∨ (((p3 → (p3 → (p2 ∧ True))) → ((False → p3) → (p2 → (p4 ∨ False)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192369984884150666914636293062 : (((p4 → ((p2 ∨ p4) ∨ ((p4 ∧ p3) ∨ p2))) ∧ p2) → (((p4 → p5) ∧ ((False ∨ (((p4 ∨ True) ∧ p1) → p2)) → (p5 ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_695072360596285335033912204803 : (((((p4 → ((p1 ∧ ((p2 → p2) → ((p2 ∨ p3) ∨ p2))) ∨ False)) ∧ True) → (((p2 ∧ p1) → (p4 → p5)) ∧ ((p1 → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179832917495889571496665824790 : (((p5 ∧ (((p4 → (p3 → False)) ∨ (True → (p2 → p1))) → False)) ∧ p5) → ((p1 ∧ ((p2 ∧ (p2 → (True ∧ (p1 ∧ p1)))) ∨ p4)) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44413149273347183692500768995 : ((((((p5 ∧ p5) ∧ p5) → (((p2 ∨ p5) ∨ ((False ∧ True) ∧ False)) ∧ False)) → (p1 ∨ ((((p4 ∧ p3) ∨ p1) → True) ∧ p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4164808180270482855924745945 : (p4 ∨ (((p3 → (p1 → (p5 ∨ ((((p4 → True) → p4) → (True ∨ True)) ∧ p4)))) ∨ p4) ∨ (True ∧ (False ∨ (True ∧ (False → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701110824466084894797689547353 : ((((((p3 ∧ p5) → (True ∨ ((p4 ∨ p2) → p4))) → True) ∧ (((p2 ∨ (p5 ∨ (p3 ∨ (p5 ∧ (p2 → False))))) ∨ (True ∨ p3)) ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_655495095700648458335169543349 : (((((((p3 ∨ (p3 ∨ ((p2 ∨ p5) ∧ True))) → ((p5 → (((p2 → p4) ∨ p3) ∧ p2)) ∨ p4)) ∧ p3) → (p5 ∨ p4)) ∨ (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178812841566515205026555529716 : (((p3 ∧ (p2 ∧ p4)) ∨ ((p5 ∨ (p4 ∧ (True ∨ p4))) ∨ (p5 ∨ p3))) ∨ ((True ∨ (p3 ∨ ((p1 ∨ (p4 ∧ (p1 → p5))) → False))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57084896779555357347251913121 : ((((p1 ∧ p4) ∧ p5) ∨ (p3 → (((((p5 → p1) → p2) → (p4 ∧ (((p1 → (p5 ∧ p2)) ∨ False) ∧ p1))) ∨ False) ∧ (True → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193050289784843815340427641474 : (((False → (p4 → (True ∧ (p2 ∧ p2)))) → (p1 ∧ True)) → ((((p5 → p2) ∧ p2) → ((((p5 → False) → True) → p5) → p1)) ∨ (p5 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p4 → (True ∧ (p2 ∧ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94978060617178152714763408679 : ((p4 ∧ ((((False ∨ ((True ∨ p4) ∧ (p4 ∨ ((False ∨ ((p4 ∧ (p4 → p1)) ∧ p3)) ∨ (p5 ∧ False))))) ∨ p4) ∧ (True → p5)) ∧ p4)) → p5) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h16 := h7 h15
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- Conjunctions on the left can always be decomposed.
              let h21 := h20.left
              let h22 := h20.right
              -- Conjunctions on the left can always be decomposed.
              let h23 := h21.left
              let h24 := h21.right
              -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
              have h25 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h7, we can now drive its conclusion.
              let h26 := h7 h25
              -- One of the premise coincides with the conclusion.
              exact h26
          case inr h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- False on the left can always be used.
            apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h31 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h32 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h33 := h7 h32
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h36 =>
              -- False on the left can always be used.
              apply False.elim h36
            case inr h37 =>
              -- Conjunctions on the left can always be decomposed.
              let h38 := h37.left
              let h39 := h37.right
              -- Conjunctions on the left can always be decomposed.
              let h40 := h38.left
              let h41 := h38.right
              -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
              have h42 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h7, we can now drive its conclusion.
              let h43 := h7 h42
              -- One of the premise coincides with the conclusion.
              exact h43
          case inr h44 =>
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- False on the left can always be used.
            apply False.elim h46
  case inr h47 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h48 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h49 := h7 h48
    -- One of the premise coincides with the conclusion.
    exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58285721611887688757309873472 : (((True ∨ False) ∧ (p3 ∧ (((((p3 ∨ (p5 ∨ (p5 ∧ (True ∨ (p2 ∧ (p4 ∨ p2)))))) ∨ p3) ∧ p5) ∧ (p4 → p5)) ∨ (p3 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811948320667313711650303075387 : ((((((p1 ∧ (((True ∧ (((True ∧ ((p1 → p1) → (p4 → p2))) ∧ (False ∨ p3)) ∨ False)) → (p4 ∧ p5)) ∧ p3)) ∧ True) ∧ p2) ∧ p2) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ (((True ∧ ((p1 → p1) → (p4 → p2))) ∧ (False ∨ p3)) ∨ False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h15 := h10 h12
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47121878516504183413530442521 : ((((((False ∧ ((p4 ∨ (((p2 ∨ (p4 ∧ (p4 → p1))) → p1) → p3)) ∨ True)) → p3) ∧ p3) → (p5 ∧ (True ∨ p5))) ∨ (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44520352748699208063785086775 : (((((p5 ∨ True) → (p3 → (True ∨ ((p5 ∧ p3) → False)))) ∨ (p4 ∧ (p3 → (False ∧ (p2 ∧ (p4 → ((p2 ∧ p2) → p2))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219324789528530381677181596844 : ((p2 ∨ (p4 ∧ (p1 ∧ p3))) → ((p4 → (((((p1 → ((True ∨ True) → p5)) ∧ p4) ∨ (p2 ∧ True)) → (False ∧ (p4 ∨ False))) ∨ True)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191799627881106746462553453123 : ((p2 ∨ ((((p5 ∨ p2) → p4) ∨ (p3 → p4)) → p4)) ∨ (p2 → (p5 → ((((p5 ∨ p4) ∨ p4) ∧ False) ∨ (p5 ∧ ((p2 → p5) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135993179274874695280936831881 : ((((True ∨ p1) ∧ ((p2 → p2) → (p5 → (p4 ∨ p2)))) ∨ (((p2 ∨ p3) → p2) ∨ ((False ∧ (p2 → p1)) → p5))) ∨ ((True → p5) ∧ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219038783076572417404291618423 : ((p5 ∧ ((p1 → p1) ∨ p5)) → (((((p4 ∧ False) ∨ p4) → ((p4 → (p3 ∨ p2)) ∨ (True → p3))) → ((p5 ∨ True) ∧ p3)) ∨ (True ∧ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260848376729969535484662966225 : ((p4 → True) → ((((p5 → p5) ∧ (True → p3)) ∨ ((p3 → ((p5 ∨ p2) ∧ (p2 ∨ p4))) ∨ p1)) ∨ (((p5 → (p3 → True)) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45726343947546969933586045623 : (((True → (True ∧ ((p2 ∧ p5) ∨ (((p2 → (False ∨ p5)) ∧ (((((p5 ∨ p2) → p5) ∨ p1) → p3) ∨ True)) ∧ (False ∨ p4))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187221904268621652861977102275 : (((p2 → p1) → (p1 → ((False ∨ (p1 ∨ (False ∧ p1))) → True))) → ((p5 → (p3 ∧ (p2 ∧ ((p3 ∨ False) ∧ (True ∨ False))))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786405913848505507528875236508 : (((p4 ∨ (((False → p2) → ((((p1 ∨ (p2 ∧ (False → p1))) ∨ p4) ∧ p3) → False)) ∧ (False → (((p1 ∧ p2) ∨ p1) → (False ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46247570595862383011868306045 : ((((p3 → (p1 ∧ ((p2 ∧ p4) ∧ ((p1 ∧ (((p4 ∧ (True ∨ p4)) ∧ p4) ∧ True)) → (p1 ∧ p4))))) ∨ (True → p2)) ∧ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649366703480498485550835452203 : (((((p1 → (p4 → ((p4 ∨ (True ∨ p4)) ∧ (((p2 ∨ ((p3 → True) ∧ (p2 ∨ (p4 ∧ p1)))) ∨ True) ∨ False)))) → p4) ∧ (False → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157818829952896430200729715004 : ((((False ∧ (((p1 ∨ p1) ∧ False) ∨ p2)) ∨ ((False → p2) → p4)) → (False ∧ ((p1 → p1) ∧ p1))) ∨ ((p3 ∨ (p5 → (p5 ∨ False))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119119958754777817244837930774 : ((p1 → (False ∧ ((p5 ∨ ((p5 ∨ False) ∧ (p3 ∧ ((p1 → ((True ∧ p4) ∧ p1)) ∨ p4)))) ∨ ((p5 ∧ p5) ∨ (True ∨ p1))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318464217889185461284372955249 : (p4 ∨ ((((False ∨ (((True → ((p1 ∨ True) ∨ (p5 ∧ p5))) ∧ True) ∨ True)) → (((p3 ∧ True) ∧ False) ∨ p5)) → (p3 ∨ p5)) ∧ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((True → ((p1 ∨ True) ∨ (p5 ∧ p5))) ∧ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



