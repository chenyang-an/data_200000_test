variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186038892104306421035109050503 : (((((p2 ∧ p4) ∨ ((False ∨ True) ∨ (p5 ∧ p4))) ∧ p2) ∨ True) → ((p3 → ((p2 ∨ ((p1 ∨ False) ∨ ((p2 ∨ False) ∧ p5))) ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662497319999107270783938364336 : (((((p1 → ((False ∨ (p2 ∨ p4)) → p4)) ∧ ((((p2 ∨ (p2 ∧ p3)) ∧ p2) ∧ (((True ∨ p5) → p4) ∨ p2)) ∨ False)) → (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261811877568149174524487817763 : (True ∧ (((((((p2 → (p3 ∧ (p2 ∧ (p5 ∧ ((p1 ∨ ((True → p3) → p4)) ∨ False))))) → p1) → p2) ∨ p2) ∧ p2) → (p4 ∨ p2)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48408858005196326904565142368 : (((p1 → (p5 → (p1 ∧ (((p2 → ((p4 ∨ p3) ∨ (True → (p1 ∧ (p5 ∨ False))))) → True) ∧ (p1 ∧ (p2 ∧ p3)))))) → (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312311046254548635381138645706 : (p2 ∨ (p2 → ((((p2 ∨ p1) ∧ ((p5 ∨ p3) ∧ (p4 ∨ p2))) ∨ ((p5 ∧ p5) → p5)) → (p1 → (((p5 ∧ False) ∨ (False → p5)) ∧ True))))) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h6.left
      let h22 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- False on the left can always be used.
          apply False.elim h32
  case inr h33 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h34
    -- False on the left can always be used.
    apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302602657444395463714319867181 : (False ∨ (p1 ∨ (p2 ∨ ((False ∧ ((p5 → p3) ∨ p4)) ∨ ((((p2 ∨ (p4 ∨ p5)) → ((False ∨ False) ∧ p1)) ∧ (True ∧ p2)) → (p5 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (p4 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h15 : (p2 ∨ (p4 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h16 := h11 h15
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671558837774652229300031089544 : ((((p4 → (True ∧ (((p2 ∨ (((False ∨ (p4 → p3)) → p1) ∨ ((p1 ∧ p1) ∨ p2))) → (p1 ∧ p2)) ∧ p4))) ∨ ((p1 ∨ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117301274343464433779769429637 : ((False ∧ (((p2 → (p5 ∨ ((((p1 ∧ p1) ∨ p2) ∧ ((p4 ∧ p5) → True)) → ((p1 ∨ p5) ∧ p3)))) ∨ p2) → (False ∨ p3))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345513492323444332580419110745 : (p3 → ((((p1 → ((p1 → (p2 ∧ p5)) ∨ p1)) ∨ (True ∨ (p5 ∧ (p1 → True)))) → ((p5 → (False → p5)) → ((p2 ∨ p3) ∨ p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346779238465041329238792701437 : (p3 → ((((((((p5 ∧ (p3 ∨ p1)) ∨ p4) ∧ p2) → p5) → (p2 ∧ p1)) ∨ False) ∨ ((p3 ∧ p1) ∨ p5)) ∨ (((p2 ∧ True) → p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53249732173122595552978459553 : ((((p3 ∨ p5) ∧ (p5 ∨ (((p2 → p4) ∧ (True → p1)) → p5))) ∨ (False → (p1 ∨ (p3 ∧ ((((p1 ∧ False) ∨ p2) ∨ True) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20274144260126890998418439802 : ((((p5 ∧ p2) ∨ (p3 ∧ ((((False → p4) ∧ (p3 ∧ p2)) ∨ p1) ∧ True))) ∨ (((p3 ∨ False) → ((True ∧ True) → p3)) ∨ (True → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225594204720034367015991299736 : (((False → p4) ∧ p5) ∨ (((((p1 ∨ True) ∨ p3) → ((p4 ∨ (False ∨ True)) ∧ False)) ∧ ((p2 → (False → False)) ∨ ((p2 ∧ p1) ∧ True))) → p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 ∨ True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : ((p1 ∨ True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242309331243062760891267375320 : ((p2 → p2) ∧ ((p2 ∨ ((p5 ∧ p3) ∨ ((p4 ∨ ((False → ((p2 → (p1 ∧ p1)) ∨ p4)) ∧ p5)) ∨ ((False → True) ∨ (p3 → p1))))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148129111198233304867097791377 : ((((True → False) ∧ ((((p2 ∧ p2) → (p1 → p3)) ∨ p5) ∧ (p5 → (p2 ∧ (p2 ∨ p4))))) → (p4 ∨ p4)) ∨ (((p4 ∧ p5) → p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315716328919276710025117867448 : (p3 ∨ ((True → False) ∨ ((((False ∨ ((((p4 ∨ (p3 ∧ True)) → p5) → (p5 → (p1 → (False ∨ True)))) → p4)) → p4) → (False ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38525510412263977941703300520 : (((((True ∨ True) ∧ ((p5 ∨ (((p1 → True) → True) ∨ p4)) → p2)) → ((p3 ∨ ((p2 → ((p1 ∨ p4) ∨ p5)) → p2)) ∨ True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112854511981142472206958691106 : (((((p5 ∧ p2) ∧ p3) ∨ (((p5 ∨ p5) ∧ (p4 ∨ (((p2 ∨ False) ∧ True) ∨ ((p3 → (p1 → p2)) ∨ p1)))) → p5)) → p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193479193392255433203646341151 : (((p5 ∧ True) ∨ (False → (((p3 ∧ p4) → p1) ∨ True))) → (p2 → (((True ∨ p4) ∧ ((False → False) → p1)) ∨ (p4 → (True → (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160085291358876369199192895144 : (((p2 ∨ ((((((p4 → p4) ∨ p2) ∨ p2) ∧ True) ∨ (p2 ∨ p5)) ∧ ((p1 ∨ False) ∨ p5))) → False) → (p5 → (p2 ∨ (p1 ∨ (p2 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ ((((((p4 → p4) ∨ p2) ∨ p2) ∧ True) ∨ (p2 ∨ p5)) ∧ ((p1 ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606127891314640594482528393875 : (((((((p1 ∧ ((((False ∨ False) ∨ p5) → (((p4 ∨ p1) ∨ p3) ∨ p4)) ∧ (((p4 ∧ p2) ∨ p1) ∧ p1))) ∧ p3) ∧ p4) ∧ p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_339605218272285942877684053272 : (p1 → (p2 ∨ ((False ∧ (p4 ∨ (((((p1 ∧ p2) ∧ (False ∨ p2)) ∧ (((p5 ∨ p1) ∨ p2) → p4)) ∧ True) → ((p3 ∧ False) ∧ True)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117367284658513776130423553255 : ((False ∧ (p5 ∨ (((True ∧ p4) ∨ ((p3 ∧ (False ∧ p1)) → (((p2 → ((p3 ∧ p3) → p2)) ∨ (True → p3)) ∧ p5))) → p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134543798224917371709236960023 : ((((((p4 ∨ (True ∨ (p5 ∧ (p1 ∨ (True → False))))) → p1) → (False ∧ (p5 ∧ (True → (p3 ∧ p5))))) → p1) → p3) ∨ ((True ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692763295936539062450520921693 : (((((p1 ∧ ((p4 ∧ True) ∧ p4)) ∨ ((True → p4) ∧ (p5 ∧ (p2 → p2)))) ∧ ((p4 ∨ (p3 → False)) ∧ (p4 → ((p4 → True) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520713494453512192262289697593 : ((((p5 ∨ p2) → (((((p2 ∨ p1) ∨ (False ∧ (p3 ∧ p1))) ∨ p3) → (p4 ∨ (((False ∨ p1) → (p3 → (False ∨ p2))) → True))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_223981236763871575408097396935 : ((p4 ∨ (p5 ∨ True)) ∧ (((p3 ∧ (((p3 ∧ (p1 ∧ ((True ∧ p4) ∧ (False → p2)))) → True) ∧ ((p5 → False) ∧ p1))) ∨ p3) ∨ (False → p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52439073122143917940850514353 : (((True ∧ (True → ((False ∨ ((p2 ∨ p1) ∧ (False → p4))) → (p1 → p3)))) ∧ ((((p2 ∧ p2) ∧ p1) ∧ p2) ∨ ((p2 ∨ True) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34267707219325688098854231277 : ((True → ((((((((p2 → p3) ∨ (p1 ∨ p3)) ∨ False) → p4) ∧ False) ∨ p2) ∨ True) ∨ (p5 ∨ ((p4 ∨ (p3 ∨ (p2 → False))) ∧ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614980041811042894882485271647 : (((((((p4 ∨ (p3 ∨ ((p5 ∧ p4) ∧ False))) ∧ p5) → (True ∧ (((p4 ∧ True) ∧ p5) → p4))) → (((p2 → p1) → False) ∨ True)) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115222968968614631524278362372 : (((((True ∧ ((p1 ∧ False) ∧ (p3 → p2))) ∧ p5) ∧ p3) ∨ (False ∧ (p1 ∨ ((p1 → (p2 → p5)) ∨ (p2 → (False → p1)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49060179148452238370853289664 : (((((p2 ∨ (((p3 → True) → (p1 → p4)) → (p5 → (p5 ∧ ((p1 ∧ p5) ∨ p3))))) ∧ p3) ∨ (p1 ∨ True)) ∨ (False ∨ (p2 ∨ p1))) ∨ False) := by
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
theorem thm_5_vars_124759121049089679369640438535 : ((((p4 → p3) → (p3 ∨ p3)) ∧ ((p2 ∨ ((((p1 → (p4 ∧ p5)) ∨ (p3 ∧ (p5 ∧ True))) ∨ p1) ∧ (True ∨ p2))) ∧ p1)) → (False ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309377508863323460465721829566 : (p2 ∨ (((True ∧ p3) → (((((p3 → (p3 → p1)) ∧ (False → (p1 → (p2 → p3)))) ∧ (p1 → p4)) ∨ False) → (p3 → False))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704428676139328064898174423985 : ((((((p5 ∨ p2) → p1) ∨ (((p5 ∨ True) ∨ p3) → False)) → (p4 → ((((((p1 ∧ (p1 ∧ p1)) ∧ p3) ∧ p4) ∨ p1) ∧ p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138380278575653086503720200359 : ((p4 → ((p2 ∨ p1) ∧ ((p2 ∧ ((p1 ∧ p4) ∨ True)) ∨ (((((p2 ∨ (False ∨ False)) ∧ True) ∧ False) ∨ p3) ∨ p3)))) ∨ (p5 → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198616926222668195666850707015 : ((p2 ∨ (p5 ∧ (p1 → ((p3 → p5) ∧ p2)))) ∨ ((False ∧ ((p4 ∧ p1) → (False ∧ (((False ∧ (p1 → p3)) ∧ p1) ∧ False)))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233522153457182103547679345481 : ((p1 ∨ (False ∨ p4)) → ((p2 ∧ ((((((False ∨ (True ∨ p2)) ∨ p2) ∨ False) ∧ (p3 ∨ False)) ∧ False) ∨ p1)) ∨ (p1 → (False → (False → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156830109011152106750390922282 : (((True → ((p3 ∧ False) ∧ ((True → ((p3 ∧ ((p5 → p3) ∨ (False → False))) → False)) ∧ p4))) ∧ p5) ∨ ((p5 ∨ (p1 → (p3 ∨ True))) ∨ p5)) := by
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
theorem thm_5_vars_320288797287331849455330299700 : (p4 ∨ ((p4 ∧ False) ∨ ((False ∧ ((p3 ∨ ((((p4 → p3) ∨ (p3 → p2)) → ((p5 ∨ (False ∨ p3)) ∧ (p1 ∧ p1))) ∨ False)) ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748208125090603523350515000 : ((((False ∧ False) ∧ True) ∨ ((p4 ∧ (((False ∧ p5) → (True ∧ True)) → True)) ∨ (((p2 ∧ p5) ∧ (p4 ∨ p3)) ∧ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356047305907982772258109430096 : (p5 → ((p2 ∨ (((p5 → ((p5 → p2) ∨ True)) ∨ p1) ∧ ((p1 ∧ p5) ∧ ((p2 → p4) ∨ (False ∨ p3))))) ∨ ((p3 → True) ∨ (p4 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758300530226446589516468981003 : (((p2 ∧ (((p1 → ((p1 ∧ (p3 ∧ ((p1 → (p4 ∨ p3)) ∨ (p2 ∨ p3)))) ∧ (((True → p2) ∨ p2) → (False → True)))) ∨ p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309964017512308462516271200383 : (p2 ∨ (((p1 ∨ ((False → (True ∧ p4)) ∨ True)) ∧ (((p3 → p1) ∨ p4) ∧ ((True ∨ p4) → p2))) → (p4 → (((p2 ∧ p3) → False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h20 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h21 := h18 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h23 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h24 := h18 h23
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h5.left
      let h27 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h29 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h30 := h27 h29
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h32 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h33 := h27 h32
        -- One of the premise coincides with the conclusion.
        exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225290416832400481344868653974 : (((False ∨ True) ∧ p5) ∨ (((p5 ∨ (p1 ∧ p2)) ∨ ((p1 ∧ (p2 ∧ ((p2 ∧ True) ∨ (p3 → False)))) ∨ ((True ∨ (p1 ∧ p4)) ∨ p2))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600274655925518584480612454697 : (((((p3 → p5) → (((((((p3 → (p1 ∧ (p5 → p4))) ∨ p5) ∨ (p4 ∨ (p1 ∧ p3))) ∧ p4) ∧ (p4 ∨ True)) ∨ p3) → p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594272804867030852224123698264 : (((((((p4 ∧ False) → (p3 → (((p2 → (p3 → (p3 ∨ False))) ∨ p3) → p2))) ∧ p1) ∧ ((((p4 ∧ p1) → p2) ∧ p5) ∨ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620377927691017360092210873877 : (((((p3 ∨ p3) ∨ ((p1 → (p2 ∧ ((p3 ∧ (True ∨ (p5 ∨ (p4 ∨ (((True ∧ False) → p5) ∨ p3))))) ∧ p3))) ∧ (p4 ∨ p3))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_263275583128265422295304789214 : (True ∧ ((p3 ∧ (True ∧ ((p3 ∧ (p2 ∧ ((True ∧ p3) → False))) ∧ ((p5 ∨ False) → (p3 ∧ ((p1 → (p1 ∨ p5)) ∧ p2)))))) → (False ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h24 : (True ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h25 := h23 h24
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102907148742492848124592759842 : (((((((p4 → (p2 ∧ (((((p2 ∨ True) ∧ False) ∧ p2) ∧ p3) ∨ True))) ∧ p3) → p5) → p1) ∨ (p1 → (p5 → p5))) ∨ p2) ∧ (p2 → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140103529647709398872803025877 : (((p3 ∨ (True ∨ ((True ∧ (p4 ∨ True)) ∧ ((((p1 ∨ p1) → (p1 ∧ p3)) ∨ (True → True)) ∧ p5)))) ∨ (p3 → p3)) → (p2 ∨ (p5 → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h10.left
          let h15 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h10.left
          let h22 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40548437213615038464414775956 : ((((True → ((((p5 ∧ True) ∧ ((False ∨ ((p3 ∧ False) ∨ (p2 ∨ p4))) ∧ True)) ∨ (p1 → p1)) ∨ (False ∧ (True ∨ False)))) ∨ False) ∨ p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1480673131856125743813214537 : ((((p5 ∨ ((True ∨ (p2 ∧ p2)) → (((False ∨ (p5 ∨ ((p5 ∨ True) ∨ p5))) → p3) ∨ p4))) ∨ (p1 ∧ p5)) → False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801898988490810436685046065128 : (((p2 → ((p4 → True) ∧ (((p1 → True) ∧ ((((p1 → p2) → p3) ∨ p3) ∨ (p1 → p1))) → (((p2 ∨ p2) → p4) ∨ (p4 ∨ p2))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625228539867313814235946458498 : ((((True → (p2 ∧ ((p4 ∧ p3) ∧ (p5 ∨ ((p2 ∨ (p3 → ((p1 ∧ p1) ∧ (p1 ∨ (p2 → (p2 ∨ p5)))))) ∧ (True → True)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_189878699847822104581928661419 : ((p2 → ((p1 ∨ (((p4 ∨ p1) ∨ p2) ∨ p5)) ∧ True)) ∧ (((p5 ∨ (p1 ∧ False)) → ((False ∧ (p1 ∧ ((False ∨ p4) ∧ p4))) ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67556464247064423202261621029 : ((p1 → ((False ∧ p2) ∧ (((p2 ∧ (p3 ∧ p4)) ∨ p3) ∨ ((p4 ∧ (False → True)) ∨ ((p2 → ((p4 ∨ (True → p4)) → False)) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668954328189629901347476184784 : (((((p5 ∨ ((p3 → (True → p5)) ∧ (((p3 ∧ p2) ∧ False) ∧ (((p5 → (False → p2)) ∨ p3) → False)))) ∨ p5) ∨ ((False → p1) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178345979697139611432704103821 : (((False ∧ (((p2 ∨ ((p2 → p3) ∨ p3)) → p2) ∨ p2)) ∨ (True ∨ p3)) ∨ (p2 → (p1 → ((p4 ∧ p2) ∧ ((p4 ∧ p5) → (p1 → p2)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256581299643705395446449400395 : ((p1 ∨ True) → ((p2 → ((((True ∨ (p2 ∨ p5)) ∨ True) ∨ (False ∨ ((((p3 ∨ True) ∧ False) → (p2 ∧ (p3 → p5))) ∧ True))) → p4)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347422707345183298713948612532 : (p3 → ((False ∨ ((((p1 → p4) → False) ∨ True) → p1)) → ((p4 ∨ ((((p4 ∨ p1) ∧ (p1 ∧ (True ∧ p5))) ∧ p4) ∨ (True ∨ p3))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50653591441673697559304121725 : ((((p4 ∧ (p2 → ((p5 → True) ∧ ((False ∨ p4) ∨ p5)))) → (((p4 ∧ p2) ∧ True) ∧ (p3 ∧ p1))) → (p2 ∨ (p2 ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63936303181622927850294808721 : ((False ∨ (((((p2 → ((False ∧ p4) ∨ (False ∨ (p4 → False)))) → p2) ∨ (True ∧ (True → p2))) ∧ (p5 ∨ (p2 ∨ (p2 ∧ True)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117875799125584356262123629600 : ((p5 ∧ (((p2 ∨ ((p2 ∨ ((False ∨ (p3 ∧ True)) → p4)) → (((p2 ∧ (p4 → (p4 → True))) ∨ p1) ∧ True))) ∨ p1) → False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45604420207953862987376708172 : (((p3 ∨ (((p3 ∧ p5) → True) → (((((p3 → p3) ∨ (p4 → (False → (p2 ∨ p4)))) ∧ p4) ∨ (p2 ∧ (p2 → True))) ∧ p3))) → p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∧ p5) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748573339954375025103783408247 : ((((p3 → False) → (p1 → (False ∨ ((p5 ∨ (p4 → (((False ∧ ((p4 → ((p5 → False) ∨ p2)) ∧ (p2 ∧ p5))) ∧ p3) ∨ True))) ∨ p3)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244117659047466469218797805262 : ((True ∧ p3) ∨ (p2 → (((p1 ∨ (p3 ∧ p4)) → ((p3 ∨ p5) → (((p3 → True) → (p3 → (p3 → (p2 ∧ (False ∨ False))))) ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49703242483182225725556232016 : ((((False ∨ False) → ((False ∧ ((p2 ∧ (((p3 ∨ p5) ∨ True) ∨ ((p3 → (p4 → p5)) ∨ False))) → p1)) → p5)) → (p4 ∧ (False → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672814455375460573799990653203 : ((((((((((p5 → False) → False) ∨ p2) ∧ True) → p2) ∧ ((p3 → False) ∧ (p5 ∨ p4))) ∧ ((p4 → p1) → True)) → ((p5 → p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149395241535974909981991976904 : ((True ∧ ((p2 ∨ (((p5 ∨ p5) → ((p1 → p2) → (p3 → p4))) → (p1 ∨ ((p3 ∨ p3) ∧ p5)))) ∧ p5)) ∨ ((p4 → p5) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119078388425877024748895296170 : ((p1 → ((p2 ∨ (((p3 ∧ p1) ∨ (((p2 → p5) ∧ p2) → ((p4 ∧ False) ∧ p1))) ∧ (True ∧ p4))) ∨ ((p2 ∧ p1) ∧ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61138635206249303467656641162 : ((False ∧ ((False ∧ (p2 → ((False ∨ True) → p5))) ∧ ((p4 ∨ False) ∧ ((((p1 ∨ p4) → (p4 ∨ p1)) ∧ p5) → (p2 → (p2 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179159844424957111257757098286 : ((p2 ∧ (((p5 ∨ p2) ∨ (True → True)) ∧ ((p3 ∧ (p4 → p1)) ∨ p3))) ∨ (False → ((p3 ∨ (False → True)) ∧ ((p2 ∨ p5) → (p3 ∨ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85986125791682216486524392495 : (((((p2 ∨ (True ∨ False)) → False) ∧ (True → (True → p3))) ∧ (True → ((p4 → True) ∧ ((p3 → (False → (False → (p5 ∧ p5)))) → p1)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263704974142222991624848467047 : (True ∧ ((p1 ∧ ((((p5 ∧ p4) → (False ∨ p1)) ∨ p1) ∨ (p4 → ((p3 ∧ p2) ∨ (p2 → p5))))) ∨ (((p3 ∧ (p1 ∨ p2)) ∧ p3) → True))) := by
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
theorem thm_5_vars_159667596673049177173958623572 : (((((p5 ∨ p3) ∨ ((p4 ∧ ((p4 ∧ True) ∧ ((True → p2) → p3))) → (p5 ∧ p5))) → p4) ∨ p4) → ((p2 → p4) → (p2 → (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324362636121002947358315259906 : (p5 ∨ ((((p2 → p3) ∨ (p5 ∨ p2)) → p2) ∨ (((p4 ∨ p1) ∧ p4) ∨ (False → (p4 ∧ ((p5 → False) ∨ (((p5 ∧ p4) ∨ p1) ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392042191311972652092273880528 : (((((False ∨ ((p5 → True) → p1)) → (((p2 ∨ (p5 → p4)) → p2) ∧ (((True ∨ p2) → ((p5 ∨ (p3 → True)) ∧ True)) ∨ True))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_706900773253313200332664937610 : (((((((p4 ∨ (p4 ∨ p4)) ∧ p4) ∨ p2) ∨ False) ∨ (p2 ∧ ((((p5 ∨ ((p3 → (p3 ∨ (True ∧ True))) ∨ True)) ∨ p5) ∨ p4) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336442635003883087918626598378 : (p1 → ((p4 ∨ ((p2 ∧ ((p2 → ((p2 ∧ p4) ∨ (p3 → True))) ∨ (p2 ∧ p5))) ∧ (((p3 → p1) ∧ p1) → ((p4 ∧ p1) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148446433769727909547714014908 : ((((p1 ∧ (p4 ∨ (p4 → ((p4 → p4) → (False → p5))))) ∧ p1) ∧ ((p1 ∨ ((p2 ∧ True) ∧ False)) ∧ p2)) ∨ ((p5 ∧ p1) → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231325677581517435804905839216 : (((True → p2) ∨ False) → ((((p3 ∨ p3) ∨ ((p2 ∨ p3) ∧ ((p4 ∨ ((p4 ∧ p2) ∨ (p4 ∨ (p5 ∧ p2)))) ∧ (p5 ∨ p1)))) → p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33396909656680349166821822906 : ((p4 ∨ (((True ∧ (p3 → p4)) ∨ (False ∨ (p5 ∧ (p2 → (((p4 ∨ (True → True)) → p3) ∧ False))))) ∨ ((p5 ∧ (p3 ∨ p4)) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49025101240978707812181548895 : (((((p4 → (p3 ∨ (p3 → (p3 → (p5 ∧ p2))))) ∨ (p3 ∨ ((p2 ∨ p4) ∧ (True ∧ (True → p3))))) → p3) ∨ (p4 → (True ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118822315830685096101510637214 : ((True → ((((p3 ∨ ((p3 ∧ (True ∨ ((((True ∧ p1) → (p5 → p5)) ∧ p4) → p4))) → p4)) ∨ True) → (True ∧ p1)) → p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222142327290995292320886254333 : (((p4 ∨ False) → True) ∧ (((p2 → (False ∧ ((((p2 → ((False → p2) → (True → p2))) ∧ (p3 ∨ p3)) ∧ p2) ∨ True))) ∨ (p3 ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695631104569649707514068698615 : ((((((False ∨ False) → (p5 → (False ∨ p2))) ∨ (p4 ∧ ((p4 → True) ∧ p1))) → (((p3 ∧ True) → True) ∧ ((False ∧ p5) ∨ (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346794932624232176132162562980 : (p3 → ((True ∧ ((p5 → (p4 ∧ p4)) → ((p3 ∧ (False ∧ ((p2 → (p2 ∧ True)) ∨ True))) ∨ (p2 ∧ p1)))) ∨ ((p5 ∧ (p5 ∧ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71696783259487617365437219872 : (((p2 ∧ ((((p1 → False) ∨ True) → False) ∧ (((p5 → p3) ∨ (((p2 ∨ p5) ∧ False) → p2)) ∨ ((p2 ∧ (True ∧ p1)) ∧ p5)))) ∧ p1) → p3) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : ((p1 → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h22 : ((p1 → False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h23 := h6 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140738886468350017695253279701 : ((((False ∨ ((p1 ∧ ((p3 → ((p3 ∨ True) ∨ p3)) → p1)) → True)) → True) → (False ∨ ((p5 ∧ (p5 ∧ p1)) ∧ p5))) → (p2 ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p1 ∧ ((p3 → ((p3 ∨ True) ∨ p3)) → p1)) → True)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226211723656862940189829392757 : (((p2 ∨ p2) ∨ p3) ∨ (p2 → (True ∧ (p3 ∨ (((p4 → ((((True ∨ p3) → ((p5 ∧ p5) ∨ p2)) → (p5 ∧ False)) ∨ p4)) ∧ p5) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67750983823970920466575368303 : ((p2 → ((((p5 ∨ (((p4 → p2) → (p2 ∧ False)) → ((p3 ∨ ((True ∨ (p4 ∧ p5)) → False)) ∧ p3))) ∧ (p4 → p1)) ∨ p4) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142967380810010296695726883736 : ((True → (((p5 ∨ (p5 → ((p2 ∨ (False ∧ p2)) → (p5 ∨ (((p3 ∧ p5) ∨ p2) → (p4 ∨ p2)))))) ∨ False) ∧ False)) → (p3 ∨ (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714726684166053168142803244009 : ((((True ∧ (((p1 → p1) ∧ p2) ∨ p2)) → (p3 ∧ ((p3 → ((True ∧ ((True ∧ p1) ∧ p3)) ∧ p3)) ∨ ((p5 ∧ (p2 ∧ p5)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193816937013902294891446345904 : ((p5 ∧ ((((p3 → p3) ∨ p1) ∨ False) → (p1 ∧ False))) → (((((p4 ∧ p4) ∨ p3) ∧ p3) ∨ p4) ∨ ((True ∧ (True ∧ (p3 ∧ p5))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 → p3) ∨ p1) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168384473648743499289327373689 : (((False → p3) ∨ (((False ∧ (False ∨ (p1 ∧ True))) ∧ (p5 → False)) ∨ ((p2 ∨ p5) → p2))) → ((p2 ∧ ((p2 ∧ p3) ∨ p5)) ∨ (True ∨ p3))) := by
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
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316852482730974731258398912226 : (p3 ∨ (p1 → ((((p2 ∨ False) ∧ (False ∨ (((p1 → (p5 → (True → False))) ∧ (p5 ∨ True)) ∧ p2))) ∧ (p2 ∧ (p1 ∧ (p2 ∧ p4)))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317706161091736343916903727992 : (p4 ∨ (((((((p5 → (True ∧ p3)) ∨ (p5 → p3)) ∨ (((p3 ∨ p5) → p4) ∨ (p5 → p1))) ∨ False) → (p3 → False)) ∨ (p3 ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_115807406390969881731493193205 : ((((True ∧ (p3 ∧ p3)) → p5) ∧ ((p2 ∨ (False ∧ ((False ∧ True) ∨ (p4 ∨ ((True → (p2 ∨ (True ∨ p4))) ∧ False))))) ∧ p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116138598754222562280101593165 : (((p4 ∧ (True ∨ p1)) ∧ (p1 ∨ ((((p5 ∨ False) → False) → (p4 → (p1 → p5))) ∨ ((p4 ∧ (False → p1)) ∧ (p5 → p4))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



