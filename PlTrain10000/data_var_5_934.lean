variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137993570370343015321291886930 : ((p5 ∨ (p5 ∧ (((p4 ∧ ((p2 ∨ (((False → p4) → p4) → ((True → p1) ∧ p1))) ∨ p1)) ∨ False) ∧ (p2 ∨ p5)))) ∨ (False → (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341010022950233748116805017855 : (p2 → ((p1 ∧ ((p2 ∨ (p5 ∨ (p3 ∨ p3))) ∧ (p1 ∨ ((p4 ∨ p3) ∨ ((((True ∧ True) ∧ (p2 ∧ p1)) ∧ (p5 → p5)) ∨ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778930432557414121305850131092 : (((p1 ∨ (p2 → ((p4 ∨ (((True ∧ p3) ∧ (p5 ∨ p5)) ∧ (((False ∨ (False → p1)) → (p1 ∨ ((p1 ∨ p3) ∧ p4))) ∧ p4))) ∨ p2))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696703533283103091360445901889 : (((((((p1 ∨ p1) → (((False ∧ p3) → p4) ∧ p4)) ∧ True) → p3) ∧ ((p4 ∧ (p2 ∨ p3)) ∧ ((False ∨ p2) ∧ (False → (False → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608943725475074743244922281361 : (((((((((True → (False → (True → True))) ∨ p1) ∧ p4) ∧ (p3 → True)) ∧ (True → (((p3 ∧ (True ∨ p1)) ∨ p4) ∧ False))) ∨ p2) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317893588145327860865006312659 : (p4 ∨ ((p1 ∧ ((p4 → ((p1 ∧ (p5 ∧ (p5 ∧ ((False ∨ p2) → ((p3 ∨ p2) ∨ p4))))) → (p3 ∨ (True → p4)))) → (p2 ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197741201205455924248748353968 : ((((p2 ∨ p1) → p1) ∧ ((False ∧ p3) ∧ p1)) ∨ (p2 → (((True → False) → p1) ∨ ((p4 ∨ (((False ∨ False) → p1) → p2)) → (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158535692812429433336920159317 : (((False → p5) → (p3 → ((p3 ∧ True) ∧ (p1 → ((p4 → (p3 ∧ (False ∨ (p5 ∨ p2)))) ∧ False))))) ∨ ((p1 ∧ False) → (True → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149829021425939264034612584292 : ((p1 ∨ ((True → ((p2 → (True → False)) ∧ (p1 ∧ (p4 → (((p5 ∧ p2) ∧ p4) ∧ p3))))) → (p2 ∨ p3))) ∨ ((p3 ∧ False) → (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47457848255351304212205123699 : (((p4 ∧ ((p5 ∨ p5) → ((p4 ∨ (p2 → False)) ∨ (p1 ∨ ((p4 ∧ ((p2 ∨ p5) ∨ (p5 → (p5 ∨ False)))) ∧ p5))))) ∨ (p5 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262414243302058386569321225935 : (True ∧ ((False ∧ (p2 ∨ (p1 ∨ (((((((True ∨ False) → ((p5 ∧ False) → p4)) → ((p1 ∧ p1) → p5)) → True) ∨ p2) → p5) ∨ p1)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313082847902861638942547176407 : (p3 ∨ (((((((True → p5) → True) ∧ ((p1 ∨ (p3 ∧ p4)) → (p4 ∨ ((p4 ∧ p1) ∧ p3)))) → False) ∨ (p3 → False)) ∨ (p1 → True)) ∨ p3)) := by
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
theorem thm_5_vars_158556693139570172744806644850 : ((True ∧ ((False ∨ ((((((False ∧ p3) → True) → (True ∨ (p4 ∧ True))) → p1) ∨ p3) ∧ True)) ∧ False)) ∨ ((p4 ∨ True) ∧ ((p3 ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350294589368522856480662898118 : (p4 → ((p1 ∨ ((p1 ∨ ((True → ((((False → p2) → p2) → p2) → (p3 → (False ∨ p5)))) → False)) ∧ ((False → p3) ∨ (True ∧ False)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52220272423580377905471333413 : ((((p5 ∨ p5) → ((p5 → p5) ∧ (p4 → ((False → False) → (p1 ∧ (p1 → p4)))))) → (((p2 ∧ p4) ∧ p1) ∨ (p2 ∧ (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260601579925624275333307879948 : ((p3 → p2) → (((p5 ∨ p5) ∨ (((p1 → ((False → (p1 → False)) → ((p5 → True) ∨ False))) ∧ p1) ∨ (True → p1))) ∨ ((True ∨ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765602604572210723167773547904 : (((p4 ∧ ((True → ((p4 ∨ (((p5 ∧ p3) ∧ (p4 → p1)) → (p2 ∨ p4))) ∨ p3)) ∨ (((False ∨ (p2 ∧ True)) → False) ∧ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208965119745355760533259960363 : ((True ∨ ((p2 ∨ True) ∨ (True ∧ False))) → (p5 → (False ∨ ((p1 → (p4 ∧ (((p5 → False) → False) ∨ (p2 ∧ ((p2 ∨ p1) ∨ False))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124830519935929048225862407234 : ((((False ∨ (True ∨ False)) → p1) ∨ ((p3 ∨ ((p2 → p4) ∨ (((True → (p4 → p5)) ∨ (False → (False ∧ p2))) ∨ p3))) → p5)) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234135124560662749760638361974 : ((True → (p4 ∨ p4)) → ((p3 ∨ (((((p2 ∨ p1) ∧ (p3 ∨ p4)) ∧ False) ∨ p4) ∧ p5)) → ((p1 ∨ ((p1 ∨ (True ∧ p1)) ∨ p4)) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h13
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355924146215074824406280109466 : (p5 → ((((p2 ∧ (p3 → False)) ∧ (((True ∧ p1) ∨ p3) ∧ (True → p1))) ∧ (p2 ∨ ((True ∨ p5) ∨ (p5 → p2)))) → ((False ∧ True) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h21 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h22 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h23 := h8 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h27 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h28 := h8 h27
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h30 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h31 := h8 h30
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h33 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h34 := h8 h33
        -- False on the left can always be used.
        apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810389269920571908598547944267 : (((p5 → ((p5 → ((p5 ∨ True) → (p1 → (False ∧ (p2 ∨ p4))))) → ((((p3 ∨ p3) ∧ (True ∨ (p3 ∧ (p5 ∨ p5)))) ∧ p1) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197649861685521090527630612738 : ((((p5 ∧ (False → p2)) → p4) → (p3 ∧ p5)) ∨ (False → ((((((p5 ∨ True) ∧ p1) ∨ True) → (p4 → True)) → ((p4 ∨ p1) ∨ p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301934948613036364626416994289 : (False ∨ ((False ∨ p4) → (((((((p3 ∨ p4) ∨ p2) ∧ p3) ∨ ((True ∧ (p4 ∨ True)) → False)) ∨ (False ∨ p2)) ∨ p1) ∨ (p1 ∨ (p4 → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340256544370681384391498169230 : (p1 → (p5 → (p4 ∨ ((p5 → (p2 → (((((p4 ∨ False) ∨ (p1 → p2)) → p1) → (p1 ∧ p4)) ∨ p3))) ∨ (p4 → ((p3 ∨ p2) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350016936373539311437654630489 : (p4 → ((((p4 → ((p5 ∧ (p4 ∧ (((p3 ∧ (p5 ∨ p1)) → (True ∨ (p2 ∨ True))) ∨ ((p4 ∨ p3) ∧ p4)))) ∧ p3)) ∧ p2) → p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63357949433977668957240274311 : ((p5 ∧ (p2 ∧ ((False → (False ∧ p5)) ∧ ((((p2 ∧ ((False ∧ p2) → p5)) ∨ p2) ∨ ((p2 ∧ False) ∧ ((False → p1) ∧ False))) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312259653952057782840899296466 : (p2 ∨ (p1 → ((p1 → (p4 ∨ p5)) ∨ (((((p4 ∨ p4) ∨ (True ∨ p1)) ∨ False) ∨ ((p2 ∧ (True → ((True ∨ p4) ∧ p2))) → p3)) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685375173223559309640983050476 : ((((p5 → (((False ∨ p5) → p5) ∧ ((True ∨ p1) → ((((p4 ∨ p1) ∨ p3) → p5) → False)))) ∨ ((False ∨ p5) ∧ (p1 ∨ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785021769084038504136699616609 : (((p3 ∨ (p5 → (True ∧ ((p5 ∧ (p4 ∧ p5)) → ((((True → p3) ∨ (p2 ∨ ((p3 ∧ p2) ∨ p1))) ∨ p5) → (False ∨ (p3 ∨ p5))))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h2.left
        let h13 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h2.left
          let h21 := h2.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h2.left
          let h26 := h2.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h2.left
    let h31 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73372353754268821429043718332 : (((((((p4 → False) → (((((True → p4) → (p5 → False)) → (True ∧ p4)) ∨ (False → True)) → p5)) ∨ p1) ∨ True) → (p1 ∧ p4)) ∨ False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((((p4 → False) → (((((True → p4) → (p5 → False)) → (True ∧ p4)) ∨ (False → True)) → p5)) ∨ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303119592893361188042716362388 : (False ∨ (p3 → (((p5 ∨ ((((p4 → p5) → ((False → (p4 ∨ p2)) → p4)) → p4) ∨ ((p3 → False) → p4))) → p5) ∨ ((p4 ∧ False) ∨ True)))) := by
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
theorem thm_5_vars_299271107611639121986418465344 : (False ∨ (((p4 ∨ (p2 → (p1 ∨ ((p1 ∨ ((p5 ∧ (p1 ∨ (p4 → True))) ∧ p5)) ∧ p2)))) ∨ (True ∨ (True ∨ (p5 ∧ (p2 → p2))))) ∨ p3)) := by
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
theorem thm_5_vars_608705235772895845409512623909 : (((((((True → (p4 → ((p4 ∧ (((p3 ∧ (p1 ∨ p2)) ∨ p5) → p2)) → p2))) ∧ (p5 → (p4 ∨ p5))) → (False ∨ p5)) ∨ p5) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_263970625685959343811028605120 : (True ∧ (((False ∧ ((False ∨ ((True → p4) ∧ (False ∧ p1))) ∨ p2)) ∧ p1) ∨ (False ∨ ((True ∨ (p2 → False)) ∨ ((p4 ∧ False) ∨ (p1 ∧ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228522145569435334067503150574 : ((p1 ∨ (False ∧ p3)) ∨ (((p4 ∨ ((True ∧ p1) ∧ ((p5 → (((True → False) ∨ False) ∨ p5)) → ((p3 → (p1 ∨ False)) ∨ p2)))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659276570093763276996933913202 : ((((p5 → ((p2 ∧ (False ∧ ((p3 ∨ (False ∧ (p4 → (p3 ∨ ((p3 ∨ p4) ∧ (p5 → (p1 ∨ False))))))) ∨ False))) ∧ p5)) ∨ (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218072514698206688317846098232 : (((p5 ∨ True) ∧ (p1 → True)) → (((((False ∧ (p4 → ((((False ∨ (p5 → p5)) → False) ∨ False) ∨ (p3 ∨ p2)))) ∧ p2) ∧ True) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_337523490206614747654353867149 : (p1 → (((p5 ∨ (((((True → (p3 ∧ p2)) ∧ (p5 ∨ False)) ∧ ((p3 ∨ True) ∨ p5)) ∨ p3) → p2)) ∨ p1) ∨ ((p4 ∧ (p3 ∨ p4)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665494598555985331796482036868 : ((((((p5 ∨ ((False ∨ ((p5 → ((((p2 ∧ True) ∧ p1) ∧ p5) ∧ p2)) → (p4 → p1))) ∨ p1)) ∨ True) ∨ p2) ∧ ((True → p3) → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191756265331625528472713749953 : ((False ∨ (p1 → (p2 ∨ ((p3 ∧ (p3 ∨ False)) ∨ p1)))) ∨ ((True ∨ p3) → (((True → (True → True)) ∧ (p4 ∨ (p3 ∨ p1))) ∧ (False ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178223015730653028702920535642 : (((False → (False ∧ (((p5 ∧ ((False ∧ p4) ∧ False)) ∨ False) → p3))) → p2) ∨ (p4 ∨ ((False → ((p5 → (p1 ∨ p5)) ∨ p3)) ∨ (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135500795393047602141093846726 : (((p5 ∧ (p3 ∨ ((p3 ∧ ((p4 ∨ p3) ∧ ((p5 ∨ p1) → (p3 ∨ (p5 ∨ False))))) ∧ True))) → ((p3 ∧ p2) ∧ False)) ∨ ((False → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346615264592323798068279902379 : (p3 → (((((p1 ∨ (p3 → (True ∧ p1))) ∨ False) ∧ p5) ∧ (p4 → ((((p4 → p4) ∧ p3) ∨ p4) → (p1 ∧ True)))) ∨ (True ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54801020427019893017564720959 : (((False ∨ (p1 ∧ (((p5 ∧ True) ∨ p1) ∧ p1))) → (((True → (p3 → ((p1 ∧ p4) ∧ (p4 ∨ ((False ∨ p1) ∨ True))))) ∧ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149369314162971119054478652960 : (((p1 → True) → ((((p4 → (((p5 ∨ p4) → (p4 ∧ (p3 ∧ p5))) ∨ True)) ∧ (p2 ∨ p2)) ∧ True) → p4)) ∨ (True ∨ ((p3 ∧ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706045898479249127267521500769 : (((((True ∧ p2) ∨ ((p3 → p1) ∨ (p2 ∧ p2))) ∧ (((p4 ∨ (((False ∧ p5) ∨ (False ∧ ((p2 ∨ p3) → p3))) → p2)) ∧ True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136703904722069316562391456849 : (((p1 ∧ p2) ∧ (((((p5 ∨ p5) → (p4 → p2)) ∨ (((p1 → p2) ∨ p1) ∧ True)) → p4) → ((p1 → p4) ∧ p3))) ∨ ((p1 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84114028528739978040570247163 : ((((True → p3) ∧ ((True ∨ (p4 → (p1 ∨ (((p2 ∧ p2) → p5) ∨ p5)))) → p2)) ∧ ((p5 → (p1 ∧ False)) ∨ (p5 ∧ (p4 → p4)))) → p3) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174637732523072862247229053028 : (((True → (p2 ∨ (p4 ∨ p1))) → ((((p4 → p1) → p2) → (True → p1)) → False)) → ((p3 ∧ ((p4 ∨ p4) → True)) → ((p3 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67518713065417857512747699692 : ((p1 → (((p2 → p3) → (p5 ∨ (p5 ∨ p4))) ∨ (((p1 → ((((((p2 → True) ∧ p4) → p1) → False) → True) ∧ p2)) ∧ False) → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212463781567758834204901903559 : ((p3 ∨ (False → (p1 ∨ p5))) ∧ (((((p3 ∨ p1) ∨ ((p2 ∧ p2) ∧ (p2 ∧ p1))) ∨ (p1 ∨ p1)) ∧ ((False → p1) → (p1 ∧ False))) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h9 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h9
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h15.left
      let h19 := h15.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : (False → p1) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h20
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h26 : (False → p1) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- False on the left can always be used.
        apply False.elim h27
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h28 := h4 h26
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h31 : (False → p1) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- False on the left can always be used.
        apply False.elim h32
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h33 := h4 h31
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258726232554939691403250816099 : ((True → True) → ((p4 → (p4 → ((p5 ∧ (p4 ∧ ((p2 ∨ True) ∧ False))) ∧ p3))) → ((p2 ∨ False) ∨ (((p4 → False) ∧ p3) ∨ (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300036200834114561873263354889 : (False ∨ ((p4 ∨ (((p3 ∨ p4) ∧ True) ∨ (True ∧ (False → (p3 ∧ ((True → ((False → False) → ((False ∧ True) → p4))) ∨ p4)))))) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661466512422292031739386738671 : ((((((p1 ∨ ((False ∧ p5) → (p1 ∨ ((False ∨ p1) → p3)))) → (True → ((True ∧ p2) → True))) ∧ ((p4 → p5) → p1)) → (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91154423557408447264243452647 : (((p5 → False) ∧ (((p5 ∧ ((p2 ∧ p5) ∨ (((False → p4) ∧ (True ∧ (p1 ∧ (((p3 ∨ p5) ∨ p5) ∨ p1)))) → p5))) ∧ p5) ∧ p4)) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731427912940797313073238737254 : ((((True → (True ∧ p4)) → (p2 → (((((False ∧ (p4 ∨ ((p1 → (p4 ∧ p4)) ∧ p2))) → (p2 ∧ False)) → (p2 ∧ False)) → False) ∧ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ (p4 ∨ ((p1 → (p4 ∧ p4)) ∧ p2))) → (p2 ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38499260668369974115793415821 : (((((((p2 ∨ p5) → p2) ∧ (p2 ∨ (p3 ∨ p5))) ∨ (False ∨ True)) ∨ ((False ∧ p4) ∨ ((p3 ∨ (p3 → True)) ∧ (p4 → p5)))) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_149302013967984279007077437740 : (((True ∧ p5) → (((((p5 → ((p4 ∨ p1) ∧ ((p3 → p3) ∨ p5))) → p3) ∨ False) ∨ False) ∨ (p2 → False))) ∨ (p5 → (p3 ∨ (p5 ∨ p4)))) := by
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
theorem thm_5_vars_646717771690122866400797143713 : ((((p2 → (((p4 → p3) → (p4 ∨ (p4 ∧ (((p1 ∧ (p3 ∧ p3)) ∨ (False → (True → p2))) ∧ (p4 ∧ (False ∧ p3)))))) ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207405421323181788174239496303 : (((p4 ∧ ((p2 ∧ p3) → p5)) ∨ True) → (p5 → (((((False ∧ (p3 ∨ False)) → (False ∧ True)) ∨ True) ∧ p1) → ((p2 ∧ False) ∨ (p1 ∨ p4))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761509209113272566101182918534 : (((p3 ∧ ((((p5 → ((p2 ∧ ((p2 → p1) ∨ p5)) → (((True ∨ (p2 ∨ (p2 → False))) ∨ p2) ∨ (False ∨ p4)))) → p3) ∧ p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42520608044712182236941755170 : (((False ∨ (p4 ∨ ((p2 ∨ (p1 ∨ ((p4 → p1) ∧ (((p5 ∨ p5) ∧ False) → p2)))) ∨ (p4 ∨ (((p5 → True) → False) → p4))))) ∨ p5) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148555790499941773032123508975 : (((((p4 → p5) → (p3 ∨ (True ∨ p2))) ∨ (True ∧ p5)) ∧ ((False ∨ (p4 ∧ (p4 ∧ p3))) ∨ (p4 ∧ False))) ∨ (False ∨ ((p1 ∧ p4) → p1))) := by
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
theorem thm_5_vars_51975847715560964041777617946 : ((((False ∧ p4) ∧ (p3 → (((p4 → False) ∧ p4) ∧ ((p4 → (p3 ∨ p5)) → p1)))) ∨ ((False → True) ∨ ((p2 → p5) ∨ (p1 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356368824788202856516739947296 : (p5 → ((p2 → (p3 ∧ (p3 ∧ (((p2 ∧ (p1 → (p4 ∧ p5))) ∨ p3) ∨ p2)))) ∨ ((p2 ∧ (False ∧ (p2 ∧ (p2 ∨ (p3 → p1))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165345555970914349687522611172 : ((((p2 → (p4 ∧ False)) ∨ ((p4 ∨ p2) → ((p2 ∨ p1) ∨ p3))) ∧ ((p3 ∨ True) → True)) ∨ ((True ∨ p3) ∨ (p1 → ((True ∧ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351498883171508852887026068770 : (p4 → ((((p2 → False) ∨ (False ∧ False)) → ((((p1 ∨ p1) ∨ p3) ∨ (p5 → (True ∨ p5))) ∨ p3)) ∧ (False ∨ (p1 ∨ (True ∧ (True ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66370624807517177016630605614 : ((p5 ∨ (p2 ∨ ((p3 ∨ (((p1 ∧ ((((p1 → (p4 → True)) ∧ (True ∨ True)) ∧ (p2 → p4)) → True)) ∧ p5) ∨ (p3 → False))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636334394680094765402419601293 : (((((((((p3 ∧ True) → (p2 ∧ False)) → p5) ∧ (p2 → (p1 ∨ False))) ∨ (p1 ∨ p5)) → (((p1 → p3) → (p2 ∨ p5)) → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57756590851653491440416873554 : ((((p2 → p3) → p4) → (p4 ∨ ((((False → ((False → p4) ∨ ((p3 ∧ (p3 ∧ ((p3 ∧ p5) ∧ p3))) → p5))) → True) → p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198524086661056625989440321184 : ((False ∨ ((((p2 ∨ p1) → p3) → p4) → False)) ∨ (((True → ((((p5 ∧ p2) → (((p1 ∧ False) ∨ True) ∨ True)) → p5) → p2)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189573568123293811399786415829 : ((True ∨ (False ∧ ((p3 → (True ∨ (p2 ∨ p3))) → p1))) ∧ ((p5 ∨ (((((p2 → p5) → (p4 ∨ False)) ∨ True) ∨ p3) ∨ (True ∨ p1))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345514879916017326864533667067 : (p3 → (((False → ((False ∨ (False ∨ (p1 ∨ (((p2 ∧ p3) ∧ False) → p5)))) → p4)) → ((((True ∨ False) → p1) ∨ p1) ∨ (p2 ∧ p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321049389789637816792736122228 : (p4 ∨ (p1 ∨ (((((False ∧ (p2 ∨ (p4 ∧ p2))) ∨ (((p4 ∧ (p3 → True)) ∨ p2) ∨ p3)) → (p4 ∨ (False → (False → p3)))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170132366724780732491256421153 : (((((True ∧ p5) ∨ p1) → ((False ∨ p3) ∧ p1)) ∨ (p4 → (p2 → (True → True)))) ∧ ((((p2 ∧ p4) → p5) → (p2 ∧ (p1 ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246759245779233226964499150011 : ((p5 ∧ p5) ∨ ((p1 ∨ (p2 ∨ (((True ∨ (p1 ∧ p3)) → (False → (True → p2))) ∧ (p3 ∨ True)))) ∨ ((p5 → p4) → (p4 ∧ (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156200279017772061082369961412 : ((p2 ∨ ((True → (p5 → ((p1 → p5) → p4))) → (p3 → (((p4 ∨ p3) ∧ p4) ∨ (p5 ∨ p3))))) ∧ ((p3 → True) ∨ ((p4 ∧ p2) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3931270463903290701260289016 : (False ∨ (((p3 → p1) ∨ (p3 → False)) → (((p2 → (((((p3 ∧ (False ∧ True)) ∧ p1) → p1) → True) ∨ p5)) → False) → (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    have h4 : (p2 → (((((p3 ∧ (False ∧ True)) ∧ p1) → p1) → True) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h4
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → (((((p3 ∧ (False ∧ True)) ∧ p1) → p1) → True) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h9
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p2 → (((((p3 ∧ (False ∧ True)) ∧ p1) → p1) → True) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h14
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : (p2 → (((((p3 ∧ (False ∧ True)) ∧ p1) → p1) → True) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h19
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185248605959057654682110589398 : ((p1 ∧ ((p3 → (((p2 → False) ∨ p1) → (False ∨ p1))) ∧ p1)) ∨ ((False ∧ ((p4 → ((p5 ∨ (p2 ∨ (False ∨ p1))) ∨ p4)) → False)) → p5)) := by
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
theorem thm_5_vars_218008379316325966031050832661 : (((True ∨ p1) ∧ (True ∧ p3)) → (((True → (((((p2 → p2) ∨ False) ∧ p4) ∧ True) ∨ ((False → p1) → False))) ∨ (False ∨ (True → True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184752220429091573515261822886 : ((((p4 ∨ p2) ∨ (p4 ∨ True)) ∧ ((p2 → (p5 ∨ p5)) ∨ p4)) ∨ (((True ∧ (p2 → (False → p2))) ∧ (True → (True ∨ (p4 ∨ p1)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112014735843733744172762403725 : ((((p5 → (p1 ∧ (p1 → False))) → (((p2 ∧ (p3 ∧ p1)) ∧ (p5 → (True ∧ p3))) → ((False ∨ p1) ∨ (False → p2)))) ∨ p2) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623524871530172168024364543997 : ((((False ∨ ((((False → p2) → p4) ∧ p3) → (((True ∧ p5) ∨ p1) ∨ ((((p5 ∨ (p4 → p2)) ∧ p2) → True) → (p4 ∧ p3))))) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111728577775410919384679822896 : (((((p5 ∧ p2) ∨ (((p1 → ((p4 ∧ p3) ∨ (((p1 → p3) → p3) → p4))) ∨ p1) ∧ ((p1 ∨ p2) ∨ p5))) → p2) ∨ True) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700617258251767232471879078127 : ((((p2 → ((False ∧ (((True → (True ∨ p3)) ∧ p4) → p3)) ∧ False)) → (p2 ∧ (p2 ∨ (p5 → (p4 ∨ ((False → (True ∨ p5)) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69038328440321387570812032414 : ((p5 → (((((((p1 ∨ p1) ∧ (p5 ∧ ((p5 ∨ True) ∨ (False → False)))) → p2) ∨ p4) ∨ p3) → (((p2 → p2) ∧ p4) ∧ p2)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32349637077875759727899277933 : ((p1 ∨ (p2 → ((p2 → ((p2 ∨ False) → ((p3 → ((True ∧ (True ∧ p5)) ∨ (p1 → p5))) → p5))) ∨ ((p2 → (p1 → p3)) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341091325593074035133488717236 : (p2 → ((p2 → ((((True ∨ (p1 ∨ p4)) ∧ (True → ((p1 ∧ (((p2 ∧ p3) ∧ False) ∨ False)) ∨ (p3 ∨ p2)))) ∨ (p3 ∨ p2)) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136191610983081433508198674437 : ((((p3 ∨ False) ∧ ((p1 ∧ p2) ∧ p1)) ∧ ((p5 ∨ (True ∧ ((p4 ∧ (p4 → (p5 ∨ (p4 → p3)))) ∧ False))) → True)) ∨ ((False ∨ False) → p1)) := by
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
theorem thm_5_vars_650854326100993177551407073068 : ((((((p3 → (True ∨ p3)) ∨ ((p4 → False) ∨ p4)) → (((p5 ∨ ((p4 ∨ ((False → False) ∧ p1)) → p2)) → p2) → p2)) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47197587696240427929405488057 : ((((((False ∧ ((p1 ∨ ((True ∨ p2) ∧ p2)) → False)) → p2) ∨ p2) → ((p5 ∨ False) ∨ (((False → p1) → p5) ∨ True))) ∨ (True ∧ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114084565716360866645686556540 : ((((p5 ∧ p3) ∧ ((p2 ∨ ((False → True) ∨ (False ∧ p5))) ∧ (((True ∧ False) ∧ (True ∨ p3)) ∧ p3))) ∨ ((p5 ∧ p5) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113696828053986177988032785576 : (((((p2 ∨ p5) ∨ (((p2 → False) → True) → (p3 ∨ ((True → ((p2 → (False ∧ p4)) ∧ p1)) → False)))) → True) → (p3 ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248196794381627652424973340392 : ((p2 ∨ p1) ∨ (((False → (((False ∧ p2) ∧ ((((False ∨ p1) ∧ ((p3 ∨ p2) ∨ (p2 → p4))) → (p1 ∧ p4)) ∨ p1)) ∧ p4)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59009156812508584396061250400 : (((p3 ∧ p3) ∨ ((((p4 ∨ (((p1 → p4) ∧ True) ∧ p2)) → p4) → ((p4 ∨ True) → (False ∧ p2))) → ((p3 ∨ (p3 ∨ p5)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125288355284301723960250376635 : ((((p5 → p1) ∨ p2) → (((p5 ∨ (True → ((p2 → p2) ∧ (p1 ∧ p5)))) ∨ True) ∧ ((p5 ∧ (p1 ∧ (p3 ∨ p3))) → p3))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724084044914832976659526788645 : ((((p1 ∧ (p2 → p4)) ∧ (p2 → (((True ∧ p3) ∨ (((p1 → (p4 ∧ p1)) ∧ ((True → (p3 → p2)) → (p1 → False))) ∧ False)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681350560545481824945984217237 : ((((p1 ∨ ((((p5 ∨ ((p3 ∨ (p5 ∨ p4)) → p3)) ∨ (p5 ∨ False)) ∨ (p5 ∧ (p1 ∧ p2))) ∧ p1)) → (p4 ∧ (p5 ∧ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47272018764527693720097616039 : ((((False ∨ (p3 ∨ (p5 → p4))) ∧ (p1 ∨ ((p4 ∧ (p5 ∧ p3)) ∧ ((p1 ∨ (((p3 ∧ p5) ∨ p1) → p4)) ∧ p2)))) ∨ (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



