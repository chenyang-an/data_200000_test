variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695381640526377842143657206089 : (((((((p3 ∧ ((True ∧ p1) → True)) ∧ (p1 ∨ p3)) → p4) ∧ (p2 → p3)) → (p3 → ((True ∧ (p4 ∧ p5)) ∧ (False ∧ (p3 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61764205623870321927020386287 : ((p2 ∧ ((((p1 → ((True ∨ (p3 ∧ (True ∨ ((True ∧ False) ∧ False)))) ∨ (p1 ∧ False))) ∧ (p2 ∨ (p2 → (False → False)))) → False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172148911066972726402795954988 : (((p3 → (p4 ∨ ((True → False) ∧ ((p1 ∨ True) ∨ True)))) ∧ ((p2 ∧ False) ∨ p1)) ∨ (((p4 ∧ p5) ∧ (p2 ∨ ((p5 ∨ True) ∨ p3))) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55122939425800017792744869504 : (((((p5 ∨ False) ∨ (False ∨ p4)) ∧ True) ∨ (p1 ∨ (True → (p2 → ((((False ∧ p1) ∨ False) → p3) → ((p4 ∨ (True → True)) → p2)))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199416686311733546189108863772 : ((((p5 → p2) ∨ ((p2 ∧ p4) ∧ p5)) ∨ True) → ((((p5 ∧ p2) → p4) → ((((p4 ∨ p2) ∧ p2) → p1) ∨ True)) ∨ ((p1 ∨ p5) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693486892032956975118344422943 : ((((((p2 ∨ (p4 ∧ (p3 ∨ (False → ((p4 ∨ p1) ∨ p4))))) ∨ p1) ∧ p5) ∨ (p5 → ((p3 ∧ p4) ∨ ((p4 ∨ p2) ∧ (p5 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148893842721677959517050307931 : (((True ∧ (p3 → (p1 ∨ p5))) ∨ ((((p3 ∨ (p2 ∨ (p2 ∨ ((p2 ∨ p5) ∧ p2)))) → p2) ∨ p5) ∨ p5)) ∨ ((p1 → p1) ∨ (p4 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611978953362032935501508170030 : (((((((True → ((False ∨ (p5 ∧ p4)) → p5)) ∧ ((((p1 ∧ p1) ∨ p5) ∧ p5) ∨ (p4 ∧ (p5 ∨ p2)))) ∨ p1) ∧ (p1 ∨ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247832054137957822330417109959 : ((p1 ∨ p2) ∨ (((((((p4 ∧ (p5 ∨ (False → True))) → (p2 → (True ∧ p3))) ∧ p3) → (True → (p2 ∧ (p1 ∨ p3)))) → p4) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194066268500822023804224469894 : ((True → ((False → (True ∨ ((p3 → p3) ∧ True))) ∧ p3)) → (((p4 → (p1 ∨ ((p1 ∧ p4) ∨ p5))) ∧ ((p2 ∧ p5) ∨ p5)) ∨ (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46957560837230204851767656439 : ((((((((((p4 ∨ True) ∨ p2) ∧ p3) ∨ p2) → (p3 ∧ p3)) → (p4 ∨ (False ∨ (p5 → (p3 ∨ False))))) ∧ p1) → p4) ∨ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178126973163275319999399224361 : (((((False ∧ (True → (p5 ∧ True))) ∨ p1) → (p5 → (True ∨ p3))) → p5) ∨ (((p3 → True) ∧ (p2 ∨ (p1 ∨ ((p4 ∧ p5) ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164557773437747349248993514146 : ((((p1 ∧ ((p4 → (p4 ∨ True)) ∨ p5)) → (p5 ∨ (((p5 → True) ∨ False) ∨ p1))) ∧ p1) ∨ (p3 → (p2 ∨ ((p1 ∧ p5) ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347390285045108850460398305361 : (p3 → ((False ∨ ((p1 ∨ (False → (p2 → False))) → p4)) ∨ (p1 ∨ (p2 → ((((p1 → (p1 → p5)) ∨ False) ∧ ((p1 ∧ p3) ∨ p4)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665188293135601836001242050937 : ((((((p2 ∨ (((p4 → (False ∧ True)) → p5) ∧ ((((False → p4) ∨ p4) ∧ True) ∧ (p2 ∧ False)))) ∨ p2) ∧ False) ∧ ((p2 → False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249047128231790693113229356093 : ((p4 ∨ p1) ∨ ((((p2 → (p3 ∨ (p3 → (p1 ∧ (p3 ∨ p1))))) → (p4 ∧ (((True → p5) ∨ p5) ∧ (True ∧ True)))) ∧ (True → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259457196036121767874602082150 : ((False → p4) → ((((p3 → ((True → p2) → p3)) ∧ p4) ∧ p3) → ((p2 ∨ ((p2 ∧ (p5 ∨ (False ∨ (p5 ∨ p1)))) ∨ p2)) ∨ (p2 → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314420551077241737234807334452 : (p3 ∨ (((((True ∧ p2) → ((p2 ∧ p1) ∧ (True ∧ (False ∨ p4)))) ∨ False) → ((p2 → p3) ∧ (p2 → p2))) ∨ (p4 ∨ (p3 → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178322141523286304882073591840 : (((((p1 ∧ ((p1 → False) ∧ p5)) ∧ p4) ∧ (True → True)) ∨ (p2 ∧ True)) ∨ (True → ((False ∧ ((p4 → p1) → ((p4 → False) → p3))) → p4))) := by
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
theorem thm_5_vars_179388607497287350851553171583 : ((p3 ∨ ((p1 → (((True ∧ True) ∨ p4) → (True ∨ (p4 ∧ p4)))) → p4)) ∨ ((((p3 → p1) → (p3 → p3)) ∧ (p2 → (p1 → True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174162736071145084871690781454 : (((((p5 ∨ p5) ∨ False) ∨ ((p5 ∧ True) ∧ ((p1 ∧ p3) ∨ p4))) ∨ (p4 ∨ p1)) → (((((True → p3) → (p1 ∨ p3)) ∨ p4) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
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
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
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
theorem thm_5_vars_144775937823198377135464449975 : ((((p3 ∨ (p1 ∨ p1)) ∧ (((p2 ∧ p4) ∧ (p3 → (True ∧ (p4 ∧ p1)))) ∧ p3)) ∨ ((False → p4) ∨ p3)) ∧ (p1 ∨ (False → (p4 → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164692180043433713369294857481 : (((((p3 → ((p3 ∨ ((p2 ∨ (False → (p2 ∧ False))) ∨ p2)) ∧ True)) ∧ False) ∨ False) ∨ p1) ∨ (((p5 ∨ p1) ∨ p2) ∨ (p3 ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_624598276497018676138644939868 : ((((p4 ∨ ((((((p5 ∨ p1) ∧ True) → ((True ∨ True) ∨ p4)) ∨ False) ∨ p1) → (p4 ∨ (((False ∨ (p2 ∨ p2)) ∨ True) ∧ p5)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_340147925018783525992351116157 : (p1 → (p4 → (((((p4 ∨ p4) → p2) → ((p5 ∧ ((p3 → p5) ∧ p4)) → ((False ∧ (False ∧ True)) ∧ ((p2 ∧ p5) ∧ p5)))) ∧ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110874355988814693827117637963 : (((((((p3 ∧ p5) ∨ ((p2 → ((((p3 → p1) ∨ False) → p1) ∨ (p3 ∨ p1))) → p3)) ∨ p4) ∨ (p4 ∨ False)) → p5) ∧ p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615687738429569043577187476229 : (((((((True → p1) → (False ∨ ((p4 ∨ p2) ∧ p5))) ∨ ((p4 → p3) ∨ True)) ∧ (p2 → (((True ∨ (p3 ∧ True)) → p2) ∨ p4))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342265019930690947796900374843 : (p2 → ((p5 ∨ ((((p4 → ((p5 ∧ False) ∨ (p2 ∧ True))) ∧ False) ∨ p2) ∨ ((p5 ∨ p1) ∨ True))) ∧ (p5 ∨ ((p2 ∧ (p4 ∧ p1)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299389723226713488486886462232 : (False ∨ ((True ∧ (((p2 ∨ (((p2 ∧ p1) ∨ ((p2 ∧ (p3 ∧ p5)) ∨ ((p3 → p4) ∧ p5))) ∧ (p5 ∧ p4))) ∧ p4) ∧ (p2 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228216260236491159561810824025 : ((p5 ∧ (p2 ∨ False)) ∨ ((True ∧ (((p2 ∧ p1) ∨ ((((False → p4) → p2) → False) ∧ (p1 ∨ ((p4 ∨ True) ∨ p4)))) ∨ True)) ∨ (p4 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307263096672677328035164534186 : (p1 ∨ (p2 ∨ ((p4 ∨ (((p5 ∨ ((p1 ∨ p5) ∨ (p3 ∨ p1))) ∨ (p2 ∨ True)) → False)) → ((p1 ∧ p3) ∨ (p4 ∨ ((p2 → False) ∨ p5)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p5 ∨ ((p1 ∨ p5) ∨ (p3 ∨ p1))) ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263386273735781115310361651958 : (True ∧ (((((True → (p3 ∧ ((p3 ∧ p3) ∨ (False ∧ p5)))) ∧ (p5 ∨ (p3 ∨ (p1 → True)))) ∨ p5) ∧ (False ∧ False)) ∨ (p3 → (True ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252107678496056907791287264900 : ((p4 → p2) ∨ ((((p1 ∧ p3) ∨ ((p3 ∧ p5) ∧ (True → p4))) → True) → (p1 ∨ ((p3 → False) ∨ (p4 → ((p1 → (False → False)) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181607494036887164083274792082 : ((p2 → (((p4 ∧ (True → (p4 ∨ p5))) ∨ ((False ∧ False) → p5)) ∨ p4)) → (p4 ∨ (((p3 ∧ p1) → True) → ((p5 → p2) ∨ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47625784220258074684313883050 : (((p5 → (p1 → (p3 → (((p2 ∧ p5) → False) ∨ (((True → (True ∧ (((p1 ∨ False) → True) ∧ p5))) → False) ∧ p3))))) ∨ (p3 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328298237641494893615039009490 : (True → (((True ∨ (p1 ∨ p1)) → (((True ∨ (p3 ∨ p1)) ∧ (((p2 ∨ (p2 → p5)) → False) ∧ p2)) ∨ p4)) ∨ ((p3 → (p2 ∨ p3)) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317911619698394531587093115401 : (p4 ∨ ((p4 ∧ (((p2 ∧ (p3 → p5)) ∨ False) ∧ ((((False ∨ (p3 ∨ (p5 ∧ p1))) → p4) ∧ ((p5 → p5) ∨ (p2 ∧ p5))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64686940882731436501854817811 : ((p1 ∨ (p5 ∨ (((True ∧ False) ∧ (p4 ∨ (p3 → ((p3 ∨ ((p2 ∨ (True ∨ (p1 ∧ False))) ∨ (p2 ∧ (p5 ∧ False)))) ∧ p1)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68148025853565459999525700624 : ((p3 → ((((((True ∨ (True → p5)) ∨ ((False ∧ p1) → p1)) ∨ p4) → (p5 → (p1 → p2))) ∧ (p1 ∧ ((p5 → False) → False))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687797194624454695927518709939 : (((((((True → False) ∨ (p5 → (p3 ∨ (p5 ∧ False)))) → (False ∧ p5)) → (p5 ∧ p4)) ∧ (((p3 ∨ (False ∨ (False ∨ True))) → False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300906414706089006050876732385 : (False ∨ (((p1 ∧ (((p5 → (p2 ∧ True)) ∨ p1) ∧ p2)) ∨ ((p2 ∧ p4) ∨ p5)) → (((True ∧ p4) ∧ p4) ∨ (p1 → ((p5 ∨ False) → p5))))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h20
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328536432675832091636736595145 : (True → ((True → (((p4 → ((((p3 ∧ False) → p4) ∧ False) ∨ p2)) ∧ False) ∨ (p3 ∨ p2))) ∨ (((True ∨ (True ∧ p2)) ∧ p2) → (False → p3)))) := by
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
theorem thm_5_vars_310542422029949610068189148296 : (p2 ∨ (((p5 ∧ False) → (p4 ∧ (p3 ∧ False))) → ((p4 ∨ (p2 → (((((True ∨ (False ∧ False)) ∧ (p3 ∧ p1)) → p5) → p4) → p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187256896491197432401501069473 : ((True ∧ (p5 ∧ (True → ((p3 → p5) → ((p2 ∧ p2) ∨ p2))))) → (((p2 ∧ p2) ∨ (p4 → (False ∨ p3))) ∨ ((p3 ∨ p2) ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801431937877269203309571219908 : (((p2 → ((((p5 → p4) → True) → ((p4 ∨ p5) ∨ (p1 ∨ p4))) ∨ (p3 → ((p3 → (True ∧ p4)) ∨ (p5 ∧ (True ∧ (p3 → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205200155330826977273444899279 : (((p1 → (True → p5)) ∧ (p2 ∨ p2)) ∨ (p1 ∨ (p5 → (((p4 ∨ p3) ∧ p2) ∨ (p5 ∨ (((p2 ∧ p3) ∨ (False ∧ (p4 → p2))) → p4)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257707153600857705804249362130 : ((p3 ∨ p3) → ((p3 → p3) → ((p3 ∧ ((p4 ∧ (p5 ∧ False)) ∨ p1)) ∨ ((p3 ∨ (((p5 → (p3 ∨ (p1 → True))) → p1) → p4)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178199161424942004360343105718 : (((True ∨ (p3 ∧ (((p1 ∧ p3) ∧ p2) → ((False ∧ p3) ∧ True)))) → False) ∨ (True ∨ (True → (True ∨ ((p1 ∧ (p4 ∧ (p2 ∨ False))) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181248114226227781115634936258 : ((p3 ∧ (p3 ∨ (p1 ∨ ((True ∨ (p3 ∧ p4)) ∧ ((True → p4) ∧ p1))))) → (((p2 ∨ p3) → ((p3 ∨ p1) ∧ (p5 → False))) ∨ (p2 → True))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h11.left
        let h20 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248573135070327058979048311835 : ((p3 ∨ False) ∨ (((((p1 → False) ∧ p1) → (p5 ∨ ((p4 ∨ (p5 ∧ (True ∨ True))) ∧ True))) ∨ (p5 ∧ ((True ∨ p1) ∨ False))) ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157410200446514201962922147456 : ((((False ∧ ((p5 ∧ (p3 ∨ False)) ∧ (p4 → p3))) ∧ ((p3 → True) ∧ (p1 → p1))) ∧ (True ∧ p5)) ∨ ((p3 ∨ True) ∧ ((p3 → p3) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121687105750518492800053156577 : (((((((p3 → p5) ∨ (False ∧ (p3 ∨ True))) ∧ False) ∨ False) ∨ (p2 ∨ ((p1 ∧ p2) ∨ (((False ∨ True) ∧ p2) → p2)))) → p3) → (p3 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 → p5) ∨ (False ∧ (p3 ∨ True))) ∧ False) ∨ False) ∨ (p2 ∨ ((p1 ∧ p2) ∨ (((False ∨ True) ∧ p2) → p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54890630087688834456589834801 : (((((False → p4) ∧ (p3 ∨ p4)) ∨ p4) ∧ (((((p5 ∧ p5) ∨ (p3 → (((p1 ∧ False) ∧ p5) ∨ False))) → False) ∨ p3) ∧ (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123070269984021828487663523728 : ((((True → (p1 ∧ (p3 → (False ∨ (p2 ∨ (((False ∧ (p2 ∨ p3)) → p4) ∧ (p5 ∨ p1))))))) ∧ p3) → ((p5 → True) ∧ p3)) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744803165554810052008705255862 : ((((p3 ∧ p3) → ((False ∧ ((p1 ∧ (False → ((True → ((True → (((True → p2) ∧ (p4 ∧ False)) ∨ p4)) → p1)) ∨ p5))) → p4)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27295181122867671419287074606 : (((True ∧ True) → ((((p1 ∨ (True ∧ True)) ∧ p4) ∨ p4) → ((p2 ∨ ((p2 ∨ (p5 → p5)) ∨ (p3 → ((p4 ∨ p2) → p2)))) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216039154372928861344594829136 : ((p5 ∨ ((p4 ∨ p5) → p2)) ∨ (((True → (p2 ∨ ((p1 ∧ ((True → p2) → p3)) ∨ (p2 → p1)))) ∨ ((p2 ∧ p3) ∧ False)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233650428488876993643734170750 : ((p2 ∨ (p2 ∨ p3)) → ((((p4 ∧ True) ∨ (True ∧ ((((p5 ∧ p4) → p3) ∧ False) ∨ ((((p4 ∨ p3) ∧ True) → p1) ∨ True)))) ∨ False) ∨ p4)) := by
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
theorem thm_5_vars_47182794574442560231384827790 : ((((False → (p2 ∨ ((p5 ∧ (p5 → ((p3 ∧ p4) → (p1 ∧ p5)))) → False))) → (True ∧ (p4 ∧ ((p1 ∨ p3) → p3)))) ∨ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306609411433566459605833936847 : (p1 ∨ ((p2 → p5) → (((((p3 ∧ ((p4 ∧ p3) → False)) ∧ p3) ∧ p3) ∨ ((((p5 ∧ p3) ∧ True) ∨ True) ∧ False)) ∨ (p2 → (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50768297561403720483986303292 : (((False ∨ (p1 ∧ (True → (((False → (False → (False ∧ p4))) ∨ (p1 ∨ ((p4 → p5) → True))) ∧ p2)))) → ((True → False) → (p4 ∧ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244200574640638025270891510205 : ((True ∧ p5) ∨ ((((((((True → p1) ∧ True) ∧ p1) → (p5 ∨ p4)) → p5) ∧ (p5 ∨ p5)) ∧ ((True ∨ True) → (p5 ∧ True))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234415433733422794702287444795 : ((p1 → (p5 → p3)) → (((p3 ∧ p4) ∧ ((p2 → p3) ∨ ((p5 ∧ p1) → (((False ∨ p1) → p2) ∨ p2)))) → (p3 ∨ (p2 ∨ (p4 ∨ p4))))) := by
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
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755688210121621811054309849861 : (((p1 ∧ ((((p3 → ((True → p2) ∨ False)) → (False ∧ (p4 ∧ p1))) ∨ ((p1 → (p4 ∧ p4)) ∧ ((p1 ∨ True) → (p5 ∨ True)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337697298848088348601223253509 : (p1 → ((((((p4 → p1) → False) ∧ (((False ∧ p3) ∨ p4) ∨ p3)) ∧ p2) ∧ ((p1 ∧ True) ∨ p3)) → (((p3 → (False ∨ False)) ∧ p4) ∨ p4))) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h22 : (p4 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h24 := h7 h22
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h26 : (p4 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h28 := h7 h26
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166255964036884353041284211775 : ((p3 ∧ (((p5 → ((p1 ∨ ((p2 ∨ False) ∨ p4)) ∨ p5)) ∧ p5) ∧ ((p5 ∨ p3) ∧ True))) ∨ (((((True ∧ p2) ∨ p5) → True) ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352597541102665468513655129552 : (p4 → ((p1 → p4) ∧ ((p2 ∧ p4) → (p4 → ((p5 ∧ ((p5 ∧ (p4 → True)) ∨ (p1 ∧ (p5 ∧ (p3 ∨ (False ∨ False)))))) ∨ (True ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798982741080930786083115732663 : (((p1 → ((True → False) ∨ (p2 ∨ ((p5 → (((p5 ∨ p1) → False) → ((((((False ∨ p4) ∧ p4) ∨ p1) ∧ p4) ∨ p4) ∧ p3))) ∨ True)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_725612341887497809466735337898 : (((((p3 ∧ p5) ∧ p4) ∨ (p3 → (((p3 → ((p5 → p3) → (p2 ∧ (((p1 → p4) ∧ (p4 ∧ p3)) ∧ p3)))) → (p2 ∧ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255098700332191222216253258425 : ((p4 ∧ p2) → (p2 ∧ (((((p4 ∧ False) ∨ (p2 ∧ p1)) ∧ ((True ∧ p3) → p1)) ∧ (p1 ∧ (p1 → False))) ∨ (True ∨ (False ∨ (p5 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685989631140323872410962705568 : (((((((p1 ∧ ((False ∧ (p3 ∨ False)) ∧ p2)) ∧ False) ∨ (p2 → (p3 ∨ p2))) ∨ (p2 → p4)) → (((p5 ∨ p3) ∧ True) ∧ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199612561649935236143814062573 : ((((True → (p2 ∧ (p1 → True))) → p4) → True) → (p3 → (((True ∧ p5) ∨ p1) ∨ (((p4 → (p1 → False)) ∨ ((p3 ∨ False) ∨ True)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715374428114521725469496636997 : ((((p5 → (p3 → ((p4 ∧ p2) ∨ p4))) → ((p2 ∨ (True ∧ (p3 ∨ ((((p5 ∨ False) → (p1 → True)) ∨ (p3 ∨ p2)) ∧ p1)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706745603467039202130381749201 : (((((((p5 → (p4 ∧ p3)) ∧ p3) → p2) ∧ True) ∨ (p2 ∨ (((False ∧ ((((p4 ∨ p5) ∧ True) ∨ p3) → p2)) → (p1 ∨ p2)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57849869054535996399305326745 : (((True ∨ (True ∨ p3)) → ((((True ∧ True) ∨ (False ∧ ((((True ∨ (p4 ∨ p5)) ∨ False) ∧ p4) ∧ (p3 ∨ (p5 ∧ p5))))) ∧ p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679430044761853962330622849085 : ((((p5 → (p4 ∨ ((p3 → (p2 ∧ (((((False ∨ p3) ∨ False) ∨ (p2 ∨ p2)) ∧ p5) ∨ p3))) → False))) ∨ (False → (p5 → (p3 → True)))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113500929302486995532476034424 : (((((p2 → p3) → (False → ((((p5 ∧ (p2 → p2)) ∨ False) → (False ∨ p2)) → False))) → ((p2 ∧ p5) ∨ p1)) ∨ (True ∨ True)) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217805793093804547527844822297 : (((p1 ∨ (p4 → True)) → p2) → (p2 ∧ ((((((p1 ∨ (p2 ∧ p4)) ∧ (p4 ∧ p5)) ∨ p4) ∧ (p2 ∧ (p1 ∧ (True ∨ False)))) ∨ p2) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p4 → True)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ (p4 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589784871265377206138615951181 : (((((((((True → (p4 → (p4 → (p3 ∨ (False → p1))))) ∨ (True ∨ (False ∨ (p3 ∨ True)))) ∨ p3) ∧ p3) → (False ∨ p3)) → False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40359901386745125394325595745 : (((((((((p3 ∨ True) ∧ (p3 → True)) → (p1 → p5)) ∨ (False → (p1 ∧ p4))) → ((p1 ∧ p2) → (p4 ∨ p1))) → p3) ∨ True) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313182889197626743569556393853 : (p3 ∨ (((((p2 ∨ p2) → p3) ∨ (False → p5)) ∧ (p2 ∨ (p5 ∧ (p3 → (p1 ∨ ((False → ((p1 → p3) ∧ (False ∨ p4))) → p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200022881949562812372906503273 : ((((p4 ∧ p1) → (p2 → p4)) → (p1 ∧ False)) → ((p1 ∧ ((p3 → (False → (p1 ∨ p3))) → ((True ∨ (p4 ∨ False)) ∧ False))) → (False ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → (False → (p1 ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (p3 → (False → (p1 ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254702693291160629941583530215 : ((p3 ∧ p3) → (((p3 → False) ∧ ((((p4 ∧ (p3 ∨ (p4 ∨ (p4 ∧ p3)))) ∨ (p1 → False)) ∧ ((p4 ∧ p3) ∧ (p5 ∧ p4))) → True)) → p2)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158854929576003074189781636221 : ((False ∨ ((((False ∧ p2) ∨ p3) → ((p3 → (p5 ∧ ((False → True) ∧ True))) → (p1 ∨ False))) ∧ p1)) ∨ ((((False → True) ∧ False) ∧ p5) → p2)) := by
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
theorem thm_5_vars_68567941747065862039007477583 : ((p4 → (((p3 → ((p2 ∨ p4) ∧ (((True ∨ ((p1 ∧ False) ∧ (p3 → p5))) → p3) → ((p2 → (p4 ∨ p5)) ∨ False)))) → p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313144188660225538302828046549 : (p3 ∨ (((p4 → ((p2 ∧ (True → (True ∧ p3))) → (((True → p4) → False) → (p2 ∨ False)))) → (((p3 ∨ p2) → (p1 ∨ p5)) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44696121758277413357751874413 : ((((((p4 ∨ True) ∨ p1) ∨ p1) ∧ ((True ∨ (True → ((p1 ∨ (p1 → (p3 ∧ (False ∧ p5)))) ∧ ((p4 → p4) → p1)))) → p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166325236723738144238464777215 : ((p5 ∧ ((p5 ∨ ((p1 → True) ∧ (p5 → True))) → ((p4 ∧ (p2 ∨ p1)) ∧ (p2 ∧ p3)))) ∨ (False → ((p1 ∧ p2) → ((True ∧ p4) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139028343249362645211753835591 : ((((((p1 → ((p3 ∨ (((p3 ∧ (True → p5)) ∧ (True ∧ (False ∨ False))) ∧ p4)) → False)) ∧ p4) → p2) → p4) ∨ p5) → ((p5 ∨ True) ∨ p4)) := by
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
theorem thm_5_vars_263805112420708636899290515255 : (True ∧ (((False → p5) ∧ (((p5 → True) → ((p4 ∧ ((True → p1) ∨ p4)) ∨ p1)) ∧ p3)) ∨ (((p4 ∧ (True → p4)) ∨ (p5 ∨ p1)) → True))) := by
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
theorem thm_5_vars_323944398323337671652879212045 : (p5 ∨ ((p3 ∨ ((((True ∧ p5) → p5) ∧ ((((p4 ∧ True) → p4) ∨ p3) ∨ p1)) ∨ p5)) → (p4 ∨ (((False ∨ (p1 ∨ True)) → p1) → p1)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False ∨ (p1 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h13 : (False ∨ (p1 ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h14 := h12 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h17 : (False ∨ (p1 ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h18 := h16 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (False ∨ (p1 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112931384035935250936499313883 : ((((False ∨ p3) → ((True → (p2 ∧ False)) → (p2 ∧ (((True → (False → p5)) → (p3 → True)) ∧ ((p1 ∨ p5) → False))))) → p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725223451322505316710951655471 : ((((p2 → (p4 ∨ p5)) ∧ (p3 → (p1 ∨ (((((((p1 ∨ p3) → p1) ∧ p1) → p3) → ((False → p5) → p5)) ∧ p5) ∧ (True → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46178575290224373881636234630 : (((((p4 → p5) ∧ (p5 ∧ ((p2 ∧ p5) ∨ ((False ∨ ((p5 → ((p3 ∨ p4) ∧ p4)) ∧ p1)) → (p1 ∧ p5))))) → p3) ∧ (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52927871518870478294325562618 : (((((((p4 ∨ p5) → True) ∧ (p3 ∧ p3)) → (p2 → p2)) ∧ p2) ∧ (p1 → ((((p1 → (p3 → (p4 → False))) → False) ∧ False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646147951126385400334652365873 : ((((False → ((p4 → (p5 → (((True → ((p3 ∧ ((p3 ∧ p1) ∧ p5)) ∧ p2)) → ((True ∨ p1) → p5)) → (p3 ∧ p2)))) ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177995511841671768565682951429 : (((False ∨ (((False ∧ ((False ∨ (False ∨ p1)) ∧ p1)) ∨ p4) ∨ True)) ∨ p4) ∨ ((p5 → p1) ∧ (p2 ∧ (p3 → (p1 → ((p3 ∧ p2) ∧ True)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979660236152306584304480363 : (True → ((((p5 ∨ (p3 ∧ ((p5 ∧ (True → p5)) ∨ (p5 ∨ True)))) ∧ (((False → (p2 ∨ p4)) → p4) → False)) ∨ ((p2 ∨ p5) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323260384103162378226132585289 : (p5 ∨ ((p5 ∧ (p5 ∧ ((((p4 ∨ False) ∨ ((False ∨ p2) ∨ (p3 → ((p2 ∨ p1) ∧ (p1 ∨ True))))) → p4) → (True ∧ p2)))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739513619420551801526947623398 : ((((p5 ∧ p1) ∨ (p3 ∧ ((p4 → ((((p3 ∨ p2) ∧ True) ∧ p5) → ((True ∧ False) ∨ (p2 → p3)))) → ((p4 → p3) → (False ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



