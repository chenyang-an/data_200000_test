variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314940458603975177815793148351 : (p3 ∨ ((p5 → (p5 ∧ (p2 → ((p2 ∧ (p5 ∧ p4)) ∨ p4)))) ∨ (((False ∧ (((p1 → p5) ∨ p3) → ((p3 ∧ False) ∧ p4))) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4030294544461778893748306671 : (p2 ∨ ((((p4 → ((True → p3) ∨ p2)) ∧ (((p3 ∨ p2) → (False ∧ p4)) ∧ p5)) ∧ (p4 ∧ ((p4 ∨ p3) ∨ (p2 → p2)))) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : (p3 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h17 := h14 h16
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h18 := h6 h15
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : (p3 ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h21
        -- We need to get the left conjuct of h22 based on <expert-advice>.
        let h23 := h22.left
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h25 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h26 := h6 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h29 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h30 := h4 h29
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h32 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h34 := h31 h33
        -- One of the premise coincides with the conclusion.
        exact h34
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h35 := h6 h32
      -- We need to get the left conjuct of h35 based on <expert-advice>.
      let h36 := h35.left
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h38 : (p3 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h37
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h39 := h6 h38
      -- We need to get the left conjuct of h39 based on <expert-advice>.
      let h40 := h39.left
      -- False on the left can always be used.
      apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194165515788109040818575288650 : ((p2 → (((True ∧ (True → p2)) ∨ (p5 ∨ p2)) ∨ p1)) → (True → ((p2 ∧ p4) → (False ∨ ((((p5 ∧ p1) ∧ p3) ∨ (p5 ∨ p2)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187673060406493134907620335752 : ((True → ((p5 ∧ True) → (False ∧ (((p5 ∧ p5) → p2) ∨ p4)))) → (p3 → (((True → (p5 ∧ False)) ∧ (((False → p5) → p4) ∨ True)) → False))) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733654138282630839894559059316 : ((((p5 ∧ True) ∧ (True → (p4 ∧ ((False → p5) → (False ∧ (((((True ∧ (p5 ∨ ((p2 → p4) → p1))) ∨ False) → p1) ∨ p1) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322571909504357260290538630418 : (p5 ∨ ((p4 ∨ (((((((p4 → ((p4 ∧ True) → False)) ∨ ((p2 ∨ p3) ∧ (p4 ∧ (p2 ∨ p3)))) → p4) ∧ p1) → p4) ∧ True) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148322108709727442923670790587 : (((p2 → ((False → p4) → (p2 → (p1 ∨ (p4 ∧ ((p2 ∨ (p5 ∧ p2)) ∨ p3)))))) → ((True → p1) ∨ True)) ∨ (False ∧ (True → (p1 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354657537285793508729645403483 : (p5 → (((((p4 ∨ ((p3 ∧ p1) → p1)) ∧ p5) ∧ ((p2 ∨ (False ∧ ((True ∨ p1) ∨ False))) ∨ (((False ∨ p4) ∧ p2) → p2))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172517128939509593757006408489 : ((((p1 → p2) → p1) ∧ ((p2 ∧ p2) ∨ (((p1 ∧ (True ∧ p4)) ∨ p2) ∨ p3))) ∨ (False → ((p3 ∨ (((p3 ∨ p1) ∨ p3) ∧ p5)) ∧ p2))) := by
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
theorem thm_5_vars_206377565438329903702176307333 : ((p2 ∨ (p1 → (False ∧ (True → p2)))) ∨ ((((p1 → (p1 ∧ (p3 ∧ p5))) → False) → ((p1 ∨ p4) ∧ True)) ∨ ((p2 ∨ p2) → (False → p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354917467973170113905754339756 : (p5 → ((p1 ∨ ((((p1 ∨ p2) → p5) → (((p1 ∨ p1) ∨ False) ∨ ((p4 → p1) → (True ∧ (p3 ∨ p5))))) ∨ (p5 ∧ (p3 ∧ p2)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347331044221196173664902854511 : (p3 → ((p4 → ((((p3 → (p2 ∧ p1)) → p1) ∨ p2) ∨ True)) → ((True ∧ (True → (((p2 ∧ (p5 → p4)) → (p5 → p2)) → p4))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
  have h8 : ((p2 ∧ (p5 → p4)) → (p5 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h13 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310602738158823345939229295133 : (p2 ∨ ((p4 → (False → (p3 ∨ p4))) ∧ (p4 ∨ ((p5 ∧ (p5 ∨ (p1 ∧ p1))) ∨ ((True → p4) → ((p3 ∨ (False ∧ (True → p2))) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347046490901179180147503348615 : (p3 → ((((((p2 ∨ p1) ∨ True) → p2) → (p2 → p5)) ∨ (p5 ∨ (p2 ∧ (p3 → True)))) → (((p4 ∧ False) ∨ p5) → ((p3 ∧ p3) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51122544604023969379790464082 : ((((((p2 ∧ (p5 ∧ (p1 ∧ p2))) ∨ p3) → (p3 → (((True ∨ True) → p2) → p1))) ∨ p2) ∨ (((p2 ∧ p3) → True) → (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125061083398876659399201484666 : (((p2 ∧ (p2 → False)) ∧ (((p1 → (((((p5 ∧ p1) ∧ p1) ∨ p1) ∨ True) ∧ p5)) → (p5 ∧ (p5 ∨ p3))) ∧ (p1 ∨ p5))) → (p1 ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h13.left
  let h17 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h19 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h20 := h15 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h22 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h23 := h15 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48995660657406315562625150438 : ((((False ∨ (((((False ∧ p2) ∨ p1) → p2) ∧ (p1 → False)) ∨ (((p1 ∨ p1) ∧ (False → p4)) → p4))) ∨ False) ∨ ((p1 ∧ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113718256106295575248767416412 : (((((((p4 → p3) → (((p1 ∨ p4) ∨ p1) → ((p2 ∧ False) → p3))) → p1) ∧ (p5 ∨ p1)) → (True ∧ False)) → (False ∧ p1)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227313086139970474500046876930 : (((p2 → p2) → p2) ∨ (p5 → (p2 → (((((((p4 ∨ p2) ∧ p3) ∧ (p1 ∨ (p5 → (True ∨ False)))) → p1) ∨ (p3 ∨ p5)) ∨ False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53063865588506038927838613170 : (((True ∧ (p5 ∨ (p2 ∨ (((p1 ∨ (p2 ∧ True)) → p3) → p1)))) ∧ (p3 ∧ (p2 → (((p5 ∧ ((p4 ∧ p4) ∨ p2)) ∨ p2) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198624808393095655669046807017 : ((p2 ∨ (p4 → (((p2 → p4) ∨ False) → False))) ∨ (p3 ∨ (((p3 → p5) ∧ (p1 ∨ (((False → p3) ∨ False) → True))) → ((p3 → p3) ∨ p4)))) := by
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
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90838986520848909761098303149 : (((p4 ∨ True) ∧ (True → (((True → (p1 ∧ (True → (p1 → p3)))) ∨ (((((p2 ∨ p5) → True) ∨ p5) ∧ p5) → p3)) ∧ (False ∨ False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789548318166611952594306319813 : (((p5 ∨ ((((p1 ∧ True) ∨ (p5 ∧ p1)) → ((p3 ∨ p5) ∧ p5)) → (((p2 → ((p2 ∧ (p5 → p4)) → (p2 ∨ p5))) → p2) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253754511314466785261429441651 : ((p1 ∧ p1) → (((p2 ∨ p4) ∨ p1) → ((((p2 ∨ p1) ∨ ((p3 ∧ p5) ∧ ((False ∨ (p3 ∨ p5)) ∧ (p1 → p1)))) ∧ (p3 ∨ p1)) ∧ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42961875494371477992587684769 : (((p5 → ((((p1 → ((p1 ∧ (p5 → ((p1 → (False ∧ p2)) ∧ (p4 ∨ p3)))) ∧ p3)) ∧ (p4 → (p4 ∧ False))) ∧ p2) ∨ p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61531950355890789350157449511 : ((p1 ∧ (((((p3 → ((False ∧ True) ∧ p5)) → p1) ∧ p2) → ((p5 ∧ p3) ∨ False)) → ((p4 ∨ ((p2 ∧ p2) ∧ p1)) → (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_575412314460867725392766761602 : (((p2 → ((p1 ∨ p3) ∨ ((p5 → p4) → ((((((p5 ∧ p2) ∧ (p1 ∧ False)) ∨ True) ∨ True) ∨ (p5 ∨ True)) ∨ ((p4 ∧ p3) ∧ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_658567702160121198686731421764 : ((((p2 ∨ (p4 ∨ ((p3 ∨ ((p4 → (p5 ∧ ((p4 ∨ (p5 ∧ (p3 → p5))) ∨ p1))) → (p3 → p1))) → (p4 ∧ True)))) ∨ (p3 → p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42611453795949763595406364962 : (((p3 ∨ (((p1 ∨ (p4 ∨ ((p2 ∨ p5) ∨ (((p2 → ((((p4 → False) ∨ p4) → p4) ∨ p3)) ∧ p1) → p5)))) ∧ p4) → p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49259773926521100638482099392 : (((False ∧ (p5 ∨ ((p3 ∧ (False ∨ (p5 → ((p2 ∨ True) ∨ p1)))) ∧ ((((p3 ∨ p2) → p4) ∨ p5) → p5)))) ∨ ((True ∨ p1) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259393424905070215748232188245 : ((False → p3) → ((((p1 ∧ ((p5 ∧ True) → (p4 ∧ p5))) ∨ (p2 ∧ False)) ∧ p5) ∨ ((False → (p5 ∨ (p2 ∨ True))) → ((True ∨ p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51214715973974321678660121625 : ((((p1 ∨ (p2 ∨ (p4 → ((p4 ∨ False) ∨ False)))) → (((p2 ∨ p4) ∨ p1) ∨ (True ∨ p2))) ∨ ((False ∧ False) ∧ ((p4 ∧ p5) ∧ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52790272130340748185682152501 : ((((p4 ∧ ((p1 → (p2 ∧ p5)) ∧ ((p1 ∧ p2) ∧ True))) → (p1 ∧ p3)) → (p1 ∨ (p5 → ((p5 ∧ True) → ((True ∧ p2) ∨ True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345543097373355989073829682033 : (p3 → ((((p3 → ((p5 → p4) → True)) ∧ False) ∧ (((False ∧ p2) → ((False → ((False ∨ False) ∧ ((p2 ∧ p3) ∧ False))) ∨ p4)) → p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760533654734217656873150887345 : (((p2 ∧ (p2 ∧ ((True ∧ (((((p1 ∨ ((p1 ∧ (p3 ∧ (False → p1))) ∧ p1)) → False) ∧ p4) ∧ True) ∨ p5)) → ((p4 ∨ p5) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137264043702489673523902088406 : ((p1 ∧ (p2 ∧ (True → (((p3 → True) ∨ (True ∨ (((True ∧ (p4 ∧ (p4 ∨ (False → False)))) → True) ∧ True))) → p2)))) ∨ ((True ∧ False) → False)) := by
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
theorem thm_5_vars_138957861448464472333438436854 : (((((p5 → ((p2 → p4) ∧ True)) → (((((p4 → p1) → p1) ∧ ((p5 ∧ p4) ∨ p2)) ∨ p2) ∧ True)) ∧ p5) ∨ False) → (p1 ∨ (p4 ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110843208816709668089986773032 : ((((True → ((((p4 ∨ (((p3 ∧ p1) ∧ (True ∧ (False → (False ∧ p2)))) ∨ False)) ∨ p5) → p4) ∨ (p5 → p2))) ∨ p3) ∧ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164471323467040640457558612005 : ((((((p4 ∨ p1) ∨ ((p2 → (p5 → (p1 ∨ True))) ∨ p2)) → (p4 ∧ True)) ∨ False) ∧ True) ∨ (((p2 ∨ ((p5 ∧ p1) ∧ p1)) ∧ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150150579179603470838585955489 : ((p1 → ((((p3 ∧ p5) ∧ p4) → ((p5 ∧ (p2 ∨ ((p5 → p1) → (p5 ∨ (p2 ∨ p5))))) → p5)) → False)) ∨ (p3 ∨ (True → (True ∨ False)))) := by
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
theorem thm_5_vars_303940179144270329655966752876 : (p1 ∨ (((((False → p3) ∧ True) ∧ (p2 ∨ p1)) ∨ ((p1 ∨ ((p3 ∨ (p4 ∨ (p3 ∨ p4))) ∨ (p1 → (p2 ∧ p2)))) ∨ (True ∨ p4))) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213895022264777785210037321129 : (((p4 ∨ (False ∧ p2)) ∨ p2) ∨ (((((p5 ∨ (p1 ∨ False)) ∨ ((False ∨ False) → (p2 ∧ p2))) ∨ (p4 ∨ p5)) ∧ True) ∨ ((p1 ∧ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195697759632077223148186443689 : (((p4 ∧ p2) ∨ (True ∨ (p5 ∧ (p2 ∨ False)))) ∧ (((((p5 ∧ ((p3 ∧ p5) ∨ (p4 ∨ p3))) ∨ True) → p2) → (False ∧ p2)) ∨ (True ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330315750183298643038307089687 : (True → (p1 ∨ ((p1 → (False ∧ (p1 → (((((p1 ∨ False) ∨ (False → p2)) ∧ p5) ∨ False) ∨ True)))) ∨ (((p1 → (p5 ∨ p3)) ∧ False) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248352536270719560119225354849 : ((p2 ∨ p3) ∨ ((p1 ∨ p3) ∨ (p2 ∨ (((((False ∧ (False ∧ p3)) ∧ ((p2 ∨ p5) ∧ True)) ∧ p4) → ((p2 ∧ (False ∧ p1)) → p3)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43288746787759601306586930774 : ((((((False ∧ (p4 ∧ p1)) ∨ ((((((p4 ∧ p4) → False) → p2) → (False ∨ p1)) ∨ False) → ((p3 → False) ∨ p4))) ∧ True) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588190449153413090218802962569 : ((((((((((True ∧ p5) ∨ p3) → False) ∨ p3) ∧ (True → p3)) → ((p1 → True) → (False ∧ (((True → p1) ∧ False) ∧ p5)))) ∨ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307208971598324514264565928615 : (p1 ∨ (p1 ∨ ((p3 ∧ ((p2 ∨ p5) ∧ p4)) ∨ (p3 ∨ ((p4 ∧ (((p4 ∧ (((p5 ∨ p1) → p2) ∨ (p2 ∧ p4))) ∨ False) ∧ False)) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19659434378959179377777248933 : (((False ∨ ((((((False ∨ (p1 ∧ (False ∨ p2))) → p5) → p1) ∧ p5) ∧ True) ∧ p5)) ∨ (p5 ∨ (((True → True) → (True ∨ p1)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_115036336621234979986916746608 : (((((p3 ∨ ((p4 ∨ p5) ∧ False)) ∧ ((p5 ∨ p1) ∧ p3)) ∧ p3) ∨ ((True ∧ p2) → (p3 → ((p1 ∨ (p3 ∧ p2)) ∨ p3)))) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313004406200644440061141113489 : (p3 ∨ (((((((p5 → (p3 ∧ (p1 ∨ (((p5 ∨ (p5 → p1)) → p1) ∧ False)))) → p5) ∧ p2) ∨ False) ∨ ((False ∨ p5) → True)) ∨ p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_52746218512799489190707139099 : ((((p3 ∧ (((False ∧ (p3 ∧ p1)) ∧ ((p1 ∨ p1) ∧ p1)) ∨ p5)) ∨ p1) → ((((p1 ∨ True) ∨ (p2 → p3)) ∨ True) ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157668950779213122476574550994 : ((((p5 → ((p3 ∧ (True ∧ p3)) ∧ True)) ∧ (p3 → ((p4 ∨ p3) ∨ p3))) ∨ (p1 ∧ (p4 ∨ False))) ∨ (((p5 → True) ∧ (p5 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314827039808282202142024641832 : (p3 ∨ ((((p2 ∨ p4) → (False ∨ ((p3 ∧ (p2 ∧ p5)) ∨ True))) ∨ False) ∨ (((True ∨ p5) ∧ p1) ∧ ((False ∨ ((p5 ∧ p3) ∧ p3)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_111685732293188794111135585789 : (((((((p2 ∨ (p4 → (p5 ∧ ((True ∧ True) ∧ p3)))) ∨ ((p4 → False) ∨ (p2 ∨ (p2 ∨ p3)))) → p5) ∨ p1) → p3) ∨ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708117852034283582207999567248 : ((((True → (((p4 ∨ (p5 ∨ p1)) ∧ p2) ∨ p4)) ∨ ((p5 ∨ ((((p5 → p3) ∧ ((p5 ∨ p3) → p5)) ∧ p1) ∨ (False → False))) ∨ p5)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187140296714235630961987135958 : (((p4 ∨ p4) ∨ ((p5 → ((True ∧ p1) ∧ p1)) ∨ (False ∨ p1))) → (p3 ∨ (False ∨ ((p2 ∨ (((False ∧ False) → (True → p5)) → True)) ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625893727500061395587775922856 : ((((p2 → ((p2 → (p5 ∨ ((p2 → (True ∨ p2)) → ((((p4 ∨ p1) → (p3 → p2)) → ((p2 ∨ p1) ∨ p4)) ∧ p4)))) ∨ p2)) ∨ p2) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51276629562696467900030123694 : (((False ∧ (p1 ∧ (p2 ∧ (((p1 ∧ p3) ∨ ((p4 → ((p1 ∧ p3) → p2)) ∨ False)) ∧ p3)))) ∨ (((p5 ∧ False) ∧ False) → (True ∧ p3))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808263326261576557716308245813 : (((p4 → (p5 ∧ ((p5 ∨ (((((p1 ∧ p5) → (p5 ∧ (p2 ∨ (p2 ∨ p5)))) ∨ p3) → (False ∨ p2)) ∨ p1)) ∨ (False → (p4 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782509443984216835496436638420 : (((p3 ∨ (((False ∧ p4) ∧ ((False ∧ p1) ∨ (p4 → ((p1 → (((p3 ∧ (p5 → True)) ∧ p4) ∧ p2)) → ((p1 ∨ p5) ∧ p2))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178143941788204132254323608556 : (((((p4 → p5) ∨ p2) ∧ (p1 ∨ ((p5 ∧ p5) ∧ (p5 ∧ p1)))) → p3) ∨ ((((p1 ∧ p4) ∨ False) ∧ (p2 → p5)) → ((p4 ∧ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179447823968321557463458655641 : ((p5 ∨ ((((p3 ∨ p5) → p3) → (p1 → (p2 → False))) ∧ (p5 ∧ p5))) ∨ (((True ∧ (((p2 → p2) → (p3 ∨ False)) → p2)) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42578560204543639341598047578 : (((p2 ∨ ((p4 → (((p4 ∨ ((p1 → (p4 ∨ (((False → p1) → True) ∧ (p5 ∨ p4)))) ∨ p2)) → p1) ∨ False)) → (True → p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608180195236527465724129269137 : ((((((p1 ∧ (p1 → ((((p3 ∨ (p5 ∨ (p2 ∨ (False → True)))) ∧ (False ∨ (p4 ∧ True))) → (p2 ∧ p4)) ∨ True))) ∧ True) ∨ True) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_43108084825477238547981329350 : (((((True ∨ (p3 ∧ (True → ((((p1 ∧ p4) → ((p2 ∨ False) ∧ p4)) ∧ (True → True)) ∧ False)))) → (p1 ∧ (False ∨ p3))) ∧ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93776014003759431127204669699 : ((p1 ∧ ((((p4 → ((p5 ∧ p1) ∨ False)) ∧ (((p1 ∧ ((p2 ∨ p2) ∧ (True → p2))) ∧ (True ∧ (False ∧ p2))) ∨ p4)) ∨ p1) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → ((p5 ∧ p1) ∨ False)) ∧ (((p1 ∧ ((p2 ∨ p2) ∧ (True → p2))) ∧ (True ∧ (False ∧ p2))) ∨ p4)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323249275414131138225813978920 : (p5 ∨ (((p3 → p1) → (((((p1 ∧ ((False → p1) ∨ p3)) → ((p2 ∨ p2) ∧ p3)) ∧ (p4 ∨ p3)) → (p1 → p3)) → p4)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67409229413968282520598701965 : ((p1 → ((p2 ∨ ((p4 ∨ (((p2 ∧ ((((p1 → (p3 ∧ p5)) → p2) ∧ p2) → p3)) ∨ (p1 ∨ p2)) → p5)) → p4)) ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166427896315208603887257965834 : ((p1 ∨ ((p2 ∧ p1) → (True ∧ (((p3 ∧ ((True ∨ p2) ∨ True)) ∨ False) ∧ (p5 → p4))))) ∨ (((((p1 ∨ p1) → p2) → p4) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148734849934910430791731091322 : (((((p1 ∧ p4) ∧ (p4 ∧ False)) ∨ False) ∧ (False ∨ (True ∧ ((p2 ∧ (p2 ∨ (True ∧ (p2 → p2)))) → p5)))) ∨ (p3 → ((p1 ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_60385241245398662252826346085 : (((p3 → p3) → ((((p1 ∧ p2) → p4) ∨ ((p1 ∨ (False ∨ ((p2 ∧ (((p4 ∧ p1) → p4) ∧ True)) ∧ False))) ∧ (p4 → True))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735879495923386979241400221598 : ((((True → False) ∧ ((p5 ∧ ((p2 ∨ (p4 ∨ p2)) ∧ (p3 ∧ (p3 ∨ ((p5 ∨ True) ∧ p1))))) ∨ (p1 ∨ (True → (p4 ∧ (True ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342153304481106903987502555218 : (p2 → ((((((True ∨ p5) → p1) ∨ (p1 ∧ (p2 → (p2 ∨ p2)))) → ((p4 ∧ False) ∧ p4)) ∨ (p3 ∧ p3)) ∨ (False → (p3 ∨ (p2 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232365214930575573967278588533 : (((p4 → p5) → True) → ((((p1 ∧ ((p3 ∨ ((((p5 ∨ p2) ∨ p5) → (True ∧ (p3 → (p2 ∨ p1)))) ∨ p4)) → p4)) ∧ p1) ∨ p4) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∨ ((((p5 ∨ p2) ∨ p5) → (True ∧ (p3 → (p2 ∨ p1)))) ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h15 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147267189399609134685765878068 : (((((True ∧ ((p3 → ((p2 → ((p4 ∧ p3) → p1)) ∨ ((False → p4) ∨ p5))) ∧ p1)) → p4) ∨ p1) ∨ p5) ∨ ((p4 → p2) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136109194866203277235709487925 : (((((p5 ∧ p4) → p2) → (True → (p4 ∨ False))) ∨ (((p3 → p3) → p5) → ((False ∨ (True → (p5 → p3))) ∧ False))) ∨ ((p2 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801358700545509282502118684752 : (((p2 → (((p2 ∧ (p1 → ((p3 ∨ ((p3 ∨ p5) ∨ p1)) ∧ p5))) ∧ p4) ∨ ((p5 ∧ (p4 → (((p3 → True) → True) ∧ p3))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779565042531207068080538225940 : (((p2 ∨ ((p1 ∧ (p2 ∧ (p5 ∨ (p1 ∨ (((p3 → p3) ∨ p5) ∨ (p1 → ((p4 ∧ ((p3 → p2) ∧ (p2 ∨ False))) ∧ p5))))))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_721325484308131574999910620768 : (((((p5 → p3) → (p4 ∧ p4)) → (p4 ∧ (p4 → ((((((((p2 ∨ False) → p4) ∧ True) ∧ True) ∨ p4) → (p5 ∧ False)) ∨ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716271776830853501562595131358 : (((((p3 → (p4 ∧ True)) → p4) ∧ ((False ∧ (((p2 ∧ p3) ∨ p5) ∨ p3)) ∨ (p4 → (((((p4 ∧ True) ∧ False) ∨ p5) ∨ p2) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168308658007026053539790388973 : (((p4 ∨ p4) ∧ ((p3 ∧ p5) ∨ (((((p4 ∨ p2) ∧ True) ∧ p1) ∧ (p4 ∨ True)) ∧ p4))) → (True ∧ ((p4 ∧ p5) ∨ (p1 ∧ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h23
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h33
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h33
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h33
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h33
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340548509977744815596697633800 : (p2 → (((True ∧ False) ∨ (((p3 ∨ (True → ((p5 ∧ ((False ∨ ((p2 → p5) ∨ (p2 → p2))) → p5)) ∨ True))) ∨ p3) ∨ (p3 → False))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793538984625843477372190442085 : (((True → (p2 ∨ (((p1 ∨ (p4 ∧ ((((p3 → p5) ∨ ((p2 ∧ p4) → (p2 ∨ True))) → (p2 ∧ p2)) ∨ p5))) ∨ p5) ∨ (False → p4)))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682194482921428111828188257605 : ((((((True → p2) ∨ ((True → p1) ∨ (((p4 ∧ (p5 ∧ p2)) ∧ p5) ∧ (p5 ∨ p1)))) → p4) ∧ (((p1 → (False → p1)) → p5) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626929922578792710703917567014 : ((((p5 → (p1 → (p2 ∧ ((False ∨ ((p4 ∨ ((((True ∧ (p5 ∨ (p3 ∨ p5))) → p2) → p1) ∨ p3)) ∧ (False ∨ p3))) ∨ False)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_310879133464901626644423817968 : (p2 ∨ ((p2 ∨ (p3 ∨ p4)) → ((True ∨ (p2 ∧ (p1 ∨ (p2 ∧ True)))) → ((p1 ∧ ((p3 ∧ p2) → False)) → ((p4 ∧ (p4 ∧ False)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39515668747638464538416611726 : (((False ∨ ((((p2 ∧ (p3 → p3)) → (p1 ∧ p1)) → ((p1 ∧ (((p3 ∨ p2) → ((p5 ∧ p2) ∨ p2)) ∧ p2)) ∨ True)) ∨ p2)) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_312422300008087504278192974126 : (p2 ∨ (p4 → ((((((p3 ∨ p5) → (False ∨ ((False ∨ False) ∧ ((p4 ∨ p5) ∨ (p1 → p3))))) ∨ (p2 → p3)) ∨ p2) ∨ p4) ∨ (p1 ∨ False)))) := by
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
theorem thm_5_vars_137081035960703796409816322181 : ((True ∧ ((((p5 ∨ ((((False ∨ p4) ∧ p1) ∨ ((p1 ∨ (False ∨ p2)) ∨ p5)) → (p5 ∧ p2))) → False) ∧ p5) ∧ p1)) ∨ (True ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204155545575682931715043897704 : (((((False ∨ p5) ∨ p5) ∨ p3) ∧ True) ∨ (p4 ∨ (True ∨ ((((False ∨ p5) ∧ p4) ∧ ((p2 ∨ False) ∧ ((p1 ∨ (p3 → p2)) ∧ True))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652208942562526926564309698222 : ((((p2 ∧ ((p2 ∨ (((p4 → ((True → True) → False)) ∨ (p1 → p3)) ∨ p1)) ∨ ((p5 ∨ (p1 ∨ p5)) ∨ (p1 → False)))) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192655439901876157622009954878 : (((((p5 ∨ (p4 → (p1 → p4))) ∧ p1) → p1) → True) → (((True ∧ True) ∧ (((p2 ∨ ((p5 ∨ p5) ∨ True)) ∨ p5) ∧ (p2 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200683670891678255862127075823 : ((p2 ∧ (((p5 → p3) ∧ (p4 → True)) ∧ p3)) → (((p4 → True) → p1) ∨ ((p5 → (((False ∧ p3) → ((p4 ∨ p4) ∨ p5)) ∨ p4)) ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667339709855780240004133847516 : (((((p5 ∨ p1) ∨ ((((p3 ∧ ((True ∧ p1) ∨ p1)) ∨ ((p1 → True) → ((False ∨ p5) ∧ p2))) → False) ∨ p5)) ∧ (p3 ∨ (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178207940949865457645374212487 : (((p2 ∨ ((p2 → p4) → (((p2 ∨ p3) → True) ∨ (p4 ∧ p5)))) → False) ∨ (p4 → (True ∧ (p5 ∨ ((((True → p4) ∧ p4) ∨ p3) ∨ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670671934911151963986723582230 : (((((True → p2) → ((((True ∧ p3) ∨ ((p2 ∧ (p4 ∧ ((p2 ∧ (p1 ∧ p4)) ∧ p3))) ∧ p1)) → p4) ∨ p1)) ∨ (p1 → (True → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767006331445478869950030160244 : (((p4 ∧ (p1 → ((p4 → (p1 → p3)) → ((p3 ∧ (((True ∨ p5) ∧ (p5 ∨ (p5 ∧ p3))) ∧ (p1 ∨ p2))) → (p3 → (p3 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729500956533079394473569018357 : (((((p1 ∨ False) ∨ p1) → ((((p2 ∨ False) ∧ False) ∨ (((p4 ∧ ((p4 → (True ∧ True)) ∨ p2)) ∨ (p3 → True)) ∧ p1)) ∨ (False → p1))) ∨ p5) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254616854039199520681268167639 : ((p3 ∧ p1) → (False ∨ ((True → (p3 ∧ ((((p3 ∧ p5) ∨ (False → (p1 ∧ True))) → ((p3 ∧ p4) → p3)) → p2))) ∨ (p4 ∨ (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



