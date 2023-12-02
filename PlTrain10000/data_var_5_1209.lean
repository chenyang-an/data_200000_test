variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324002701771655818024626054705 : (p5 ∨ ((p5 ∧ (((p5 ∧ p4) → p5) → (p5 ∧ (((p1 → p5) ∧ True) ∨ p1)))) ∨ (((True ∨ ((p5 ∧ p2) ∨ p3)) → False) → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ ((p5 ∧ p2) ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166147471750743569830078885797 : ((False ∧ (((p2 ∧ ((p2 → p1) → ((p2 ∨ p3) → p5))) ∨ ((True ∨ p5) → p3)) ∧ False)) ∨ (p1 → (((p1 ∧ (p2 → p3)) ∧ p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112382739870064068464486504003 : ((((((p5 ∨ (((False ∧ True) → True) → ((False → p5) ∨ p3))) ∧ (True → False)) → (True → (p4 → (p1 → p5)))) ∧ True) → p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729983807841007347237268802717 : (((((p5 ∧ p5) → p4) → ((((True ∧ ((p1 → True) → p5)) ∧ p3) ∧ (p1 ∨ ((p1 ∨ (p3 → (p5 ∧ False))) ∨ False))) → (True → p1))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52006107159426911938534236309 : (((p2 ∧ (((p2 ∨ (p1 ∧ ((p5 ∧ p5) → p4))) ∧ p3) ∧ (p5 ∨ (False ∧ p4)))) ∨ ((p4 → (False → (False ∧ (p1 ∨ p5)))) ∨ p4)) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708821935922305927778221314590 : (((((((True ∨ p5) ∧ p5) ∧ True) ∧ (p3 ∧ p4)) → ((p3 → (p1 ∨ p3)) ∧ ((((p5 → p5) → p3) → (p1 ∨ p1)) → (p1 ∧ p1)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h17.left
    let h24 := h17.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h25 : ((p5 → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h26
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h27 := h15 h25
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h17.left
    let h32 := h17.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h33 : ((p5 → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h34
      -- One of the premise coincides with the conclusion.
      exact h31
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h35 := h15 h33
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h40.left
  let h43 := h40.right
  -- Disjunctions on the left can always be decomposed.
  cases h42
  case inl h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h39.left
    let h46 := h39.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h47 : ((p5 → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h48
      -- One of the premise coincides with the conclusion.
      exact h45
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h49 := h15 h47
    -- Disjunctions on the left can always be decomposed.
    cases h49
    case inl h50 =>
      -- One of the premise coincides with the conclusion.
      exact h50
    case inr h51 =>
      -- One of the premise coincides with the conclusion.
      exact h51
  case inr h52 =>
    -- Conjunctions on the left can always be decomposed.
    let h53 := h39.left
    let h54 := h39.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h55 : ((p5 → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h56
      -- One of the premise coincides with the conclusion.
      exact h53
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h57 := h15 h55
    -- Disjunctions on the left can always be decomposed.
    cases h57
    case inl h58 =>
      -- One of the premise coincides with the conclusion.
      exact h58
    case inr h59 =>
      -- One of the premise coincides with the conclusion.
      exact h59
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119858495583583356655092330369 : (((((p5 ∨ ((True → ((p4 ∨ p1) ∨ (p2 ∨ (p1 ∧ p4)))) → (p5 ∧ (p5 ∨ (p2 ∨ p4))))) ∨ p5) ∧ (p3 ∧ p3)) ∧ p4) → (False ∨ p5)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : (True → ((p4 ∨ p1) ∨ (p2 ∨ (p1 ∧ p4)))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h13
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355832013497319698127116676817 : (p5 → ((((p5 → (p5 → p2)) ∧ ((p1 ∧ ((p3 ∧ False) ∧ ((True ∨ (p1 ∧ p3)) ∧ (p4 → p1)))) ∧ True)) ∧ p5) ∨ ((p4 ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717800485853581405100844204781 : ((((((p5 ∨ p4) → p1) ∧ p1) ∨ ((((p4 ∧ (False → p2)) ∨ (p1 ∧ (((False ∧ p1) ∧ p5) ∧ False))) ∧ (p4 ∨ (False ∨ False))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185960766391513189104595193091 : (((True ∧ ((p4 ∨ False) ∨ (True → ((p2 ∧ p1) ∧ p4)))) ∧ p2) → ((p2 → p4) ∨ (p2 ∨ (((False ∧ (p2 → p3)) → p1) ∨ (p4 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669174342545807266412141745638 : (((((((True → p4) ∨ p5) → (((((p1 ∨ (p3 ∨ p5)) ∨ p3) ∧ False) ∨ (True → (p2 → p3))) ∨ p1)) → p3) ∨ ((p1 ∧ p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353221511896479349849931942036 : (p4 → (p4 ∧ (p5 → (p2 ∨ (((False ∧ ((p4 → (p1 ∨ p3)) → (True ∧ p1))) ∧ ((((False ∧ False) → p1) ∧ False) ∨ (True → p4))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56789841114306642816244697115 : ((((p5 ∧ p2) → p4) ∧ (((p2 ∨ p4) ∧ (False ∨ True)) ∨ (((True ∧ (((p4 → p3) ∨ p5) ∧ p1)) ∨ (False ∧ (p2 → p2))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147734791575953110380056253761 : ((((((p1 → p1) ∧ p3) → False) ∧ (False → ((p1 ∧ p4) ∧ (p1 ∨ (((p3 ∧ p5) ∨ p2) ∨ True))))) → p5) ∨ (((p5 ∧ p1) ∧ p1) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249248690773341487490390225615 : ((p4 ∨ p4) ∨ ((False → (False ∨ (p2 ∨ (p1 ∧ (p4 ∨ (p3 ∨ (p2 → ((False ∨ p2) ∨ p5)))))))) ∧ ((p2 ∨ (p3 ∨ (False ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117103192069648471734755033417 : (((p2 → p1) → ((p5 ∨ ((p2 → ((p3 ∨ p4) ∧ p5)) ∨ p4)) ∨ (p4 ∨ (p1 ∧ ((((p4 ∧ p5) ∨ p4) → p1) ∧ p1))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609265028726643855930807200576 : (((((((p4 → True) → p2) → ((((((p2 ∨ True) ∧ p1) ∧ (p4 ∨ (p5 → p3))) ∨ True) → ((p1 ∧ p5) ∨ True)) ∧ False)) ∨ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668908227885558581404478281147 : (((((p1 ∧ ((((((p5 ∧ False) → p5) ∨ p5) ∨ p1) ∨ p4) → (((p2 ∧ (p2 ∨ p1)) ∧ p2) ∧ p2))) ∨ p4) ∨ (p1 ∨ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184329976438923626151309145794 : ((((p2 → p4) → ((p3 → (p2 → p2)) ∧ (p3 → p1))) → p2) ∨ ((((((p2 ∧ False) ∧ ((True ∧ True) ∧ p4)) → p1) → True) ∧ p4) → p4)) := by
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
theorem thm_5_vars_352212662124195974692451420844 : (p4 → ((((p1 ∨ False) ∨ p2) ∧ p1) ∨ (p5 → ((True → (p3 ∨ ((p2 → (True ∧ (p5 ∧ (True → ((False ∧ p2) ∧ True))))) ∨ p5))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45274140167560313642973219950 : (((p2 ∧ (((True → (p5 → (p2 ∧ True))) ∨ ((False ∨ False) ∧ ((p3 ∧ (False → (p3 → ((p2 ∧ False) ∧ True)))) ∨ p4))) → p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136020126671596079622946208675 : ((((True ∧ ((p1 ∧ (p4 ∨ (p5 → p3))) ∨ p1)) → False) → ((p4 ∨ (True → ((p4 ∨ (p1 ∨ p3)) ∨ p1))) ∧ p2)) ∨ (False → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140526752714988414737712964137 : (((p2 → (p3 → ((((p2 ∧ (p1 ∨ p2)) ∧ p2) ∧ p2) → ((p5 ∨ p2) ∧ p2)))) ∧ ((p1 → p4) → (p1 ∧ p1))) → ((p3 → p1) ∨ True)) := by
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
theorem thm_5_vars_134509790352767166657772997856 : (((((False ∨ p2) → ((p4 → (((p5 ∧ (((False ∨ True) → False) ∨ (p1 ∨ p1))) → p1) → p1)) ∨ p4)) ∨ p4) → p2) ∨ ((False ∧ p3) → p2)) := by
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
theorem thm_5_vars_115082707188214346526156321771 : (((p5 ∧ ((p4 ∨ ((False ∨ (p4 → p2)) ∧ (False ∨ p1))) ∧ True)) ∨ (((p4 ∧ p2) ∨ (False ∧ ((p4 ∨ True) ∨ p4))) ∨ p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116696337387055438643816355850 : (((False ∧ p2) ∨ (((p1 ∧ ((((p5 ∨ p4) ∨ (((p3 ∨ p4) ∨ p4) ∨ (p3 ∨ False))) ∨ (True → p5)) → p5)) ∨ p5) ∨ True)) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113429048296779068954848129808 : ((((((p4 ∧ (((((p1 → (p5 ∧ p4)) → ((p1 ∧ p5) → p4)) ∨ p4) → p2) ∧ p4)) ∧ p2) ∧ True) ∨ p5) ∨ (p2 → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41335355808319041912624774328 : (((((((p2 ∨ p5) ∧ (p4 ∨ (p5 → p2))) ∨ (False ∧ ((p1 ∨ True) ∧ p1))) → False) ∨ (((True → True) ∨ p2) ∨ (p2 → p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707264735273273608595349897943 : ((((((True ∧ p4) → (False ∧ p3)) ∧ (p2 ∨ False)) ∨ (p5 ∧ (((True → ((p5 ∧ (p2 → (p1 → p5))) ∨ (True ∨ p3))) → True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315063351936237991337806401060 : (p3 ∨ ((p4 ∨ ((p2 ∨ ((p4 → True) → p4)) ∧ p1)) → (((p2 → True) ∧ True) ∧ ((p5 ∨ p3) → ((((False ∧ True) ∧ p2) ∨ True) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600203131349547004650968925867 : (((((p1 → True) → (False ∧ ((((True ∧ ((p5 → (((p5 ∧ True) ∨ True) → ((p2 ∧ False) → p4))) ∨ p5)) → False) ∨ p5) ∧ True))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599009336058182706043483399828 : (((((p3 ∨ p3) ∧ (p3 ∧ ((p5 → p2) ∧ ((p2 → (True ∨ ((((True ∧ p4) ∨ p4) ∨ ((p2 ∨ p4) ∧ p3)) ∧ p5))) ∧ p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158348088770027183171609603237 : (((p4 ∧ p5) ∧ (p1 ∨ ((p5 ∧ (p5 ∨ p5)) ∨ ((False ∧ ((False → (p4 ∧ p1)) → True)) → p1)))) ∨ ((True → p3) → ((p4 ∨ True) ∨ False))) := by
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
theorem thm_5_vars_215977900540080623494867358213 : ((p4 ∨ (True ∧ (False ∨ p2))) ∨ ((((p2 → (((p3 → (False ∨ (False → False))) ∧ p2) → p3)) ∨ p2) ∧ (p3 ∧ p5)) ∨ (p5 → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349999336285222990003248765593 : (p4 → ((((p1 ∧ p1) ∧ (((((True → p1) ∨ p5) ∧ (((p4 ∧ p1) ∨ p1) ∨ (p4 ∨ p5))) ∨ ((False ∧ p1) ∧ False)) → False)) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166476120100012615067216764926 : ((p3 ∨ ((True ∧ ((False ∧ (((p3 ∧ ((p4 → p1) ∨ False)) ∧ True) → p2)) ∨ p1)) ∨ p3)) ∨ (p2 → ((p4 ∧ (p2 → (False ∨ p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342659104554358284407690538720 : (p2 → (((p1 ∧ (((p1 ∨ p3) ∧ False) ∧ p1)) ∧ (p5 ∧ True)) ∨ ((False ∧ (False → (p2 ∨ (p4 → ((p3 → p2) → False))))) → (p1 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114930468607533721999639732796 : (((((p3 ∨ (p1 ∨ True)) ∧ (True ∧ (True ∨ p4))) ∧ (p3 ∧ (p2 ∨ p2))) → (p2 ∧ (((True → p5) ∧ p4) → (p5 → False)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389977460259976889719842017868 : (((((p2 ∨ ((((p4 ∧ p3) ∨ True) ∨ ((p4 ∨ p5) → False)) ∧ p2)) → (False ∧ (p3 ∧ (((p2 ∧ False) → p4) ∧ (p2 ∧ p1))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_114032233517681731739855775662 : (((((p2 → (p3 → (p1 ∧ (False ∧ p5)))) ∨ ((p1 ∧ ((False → p4) ∨ p2)) ∨ (True ∨ False))) → p1) ∨ ((p2 → False) → True)) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161512441127237590940187410254 : ((p4 ∧ ((p2 ∧ p5) ∨ (((True ∧ (p5 ∧ ((p1 ∧ p5) → True))) ∨ p1) ∧ ((True ∧ p4) → False)))) → (True → (p2 ∨ ((p1 ∧ p3) ∧ p5)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : (True ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h19 : (True ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129643307885681639073799797515 : ((((True → (p4 ∨ ((p4 → (True → (p1 ∧ ((False → (p5 → p2)) → p1)))) ∨ (True ∨ True)))) → (p2 ∧ p5)) → p5) ∧ (p5 → (True ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p4 ∨ ((p4 → (True → (p1 ∧ ((False → (p5 → p2)) → p1)))) ∨ (True ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204428850201683908061821388395 : (((((True ∧ p3) ∧ p5) ∧ p3) ∨ p2) ∨ ((p3 ∧ p1) ∨ ((((p3 ∨ p3) ∧ (p2 → ((p5 → p4) → (True → True)))) ∨ (p1 ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647467200556430395179257685795 : ((((p4 → (p4 ∨ (((((((p5 → p3) ∨ True) ∧ p3) ∨ p4) ∧ (((p4 ∨ p2) → p5) ∨ ((p5 → False) ∨ p2))) ∧ p1) ∧ True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40532878162206900321612224234 : ((((p2 ∨ (((p4 → ((False → p5) → p1)) → ((p5 ∨ (p1 ∨ p2)) ∨ ((p2 ∨ (p2 → p4)) ∨ (p5 ∧ p5)))) ∨ p1)) ∨ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337871422610186492694466848678 : (p1 → ((p4 ∧ ((p2 ∧ True) ∧ ((p5 ∨ ((True ∨ True) ∧ p3)) → (False ∧ p4)))) ∨ ((p5 → ((p1 ∧ False) → p3)) ∨ (True ∨ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356385474282071769816863813669 : (p5 → ((((p5 → True) ∨ (True ∨ p3)) ∧ ((((p3 → p5) ∨ p3) → p4) ∨ p4)) → (p4 → (True ∧ (((p3 ∨ p1) ∨ (False → p2)) ∨ p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309861105112474897949650559802 : (p2 ∨ ((p5 ∧ ((p3 → True) ∧ ((((((p4 → True) → (p4 ∨ p1)) ∧ p1) ∨ p3) ∨ (p4 → p3)) ∨ p4))) → ((p2 ∨ True) ∨ (False → p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621036238241736681346927646464 : (((((p1 → False) → ((p5 → (p2 → (p2 ∧ ((False → False) ∨ (p2 ∧ p5))))) → ((False ∨ (True ∧ (True → (p4 ∨ False)))) → p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149697791791639822876305754601 : ((p5 ∧ ((True → (p5 ∧ (p3 ∧ p2))) ∧ ((False ∨ (True ∧ ((True → (False ∨ p5)) → False))) ∧ (True ∧ False)))) ∨ (((p5 → False) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159229054757847260386772577891 : ((p3 → (((p3 → p2) → ((True → (p5 ∨ ((p4 → ((p5 ∧ p4) ∧ p4)) → p5))) ∧ p5)) ∧ p5)) ∨ ((True ∨ p1) ∨ (p5 ∨ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327196658805126431096022405375 : (True → ((p4 ∨ (((((True → p3) ∧ (False ∨ p2)) ∧ False) ∨ (p4 ∧ p1)) ∧ ((False → ((p1 ∧ p3) → (p4 ∧ (p1 ∧ p5)))) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200648346616292235926141209776 : ((p1 ∧ ((p2 → ((p5 → p5) ∧ True)) ∧ True)) → ((p4 ∧ ((p5 ∨ p4) → (p3 ∧ ((False ∧ False) → p1)))) ∨ (((p5 → p4) ∧ p4) ∨ p1))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45890593753332039652946080698 : (((p3 → (p5 ∨ ((p2 ∧ (False ∧ p1)) → ((((p2 → (True → True)) → ((False ∧ p2) → p1)) ∧ (p1 ∨ (True → p1))) → p5)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164778553623457591757610904996 : (((((p4 ∨ False) ∨ ((p5 ∨ p4) ∧ p5)) ∧ (p4 ∨ ((p3 → (p4 ∨ p3)) ∧ p4))) ∨ True) ∨ ((p5 ∧ True) ∧ (False → ((p1 ∧ p3) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41719827450047945846929343657 : ((((((p1 → p3) ∧ p3) ∨ p5) ∧ ((True → ((p5 ∨ (((p4 ∧ (p2 ∧ p1)) ∧ p4) ∨ (p1 ∨ False))) ∨ (p4 ∨ p2))) ∨ False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118767967019025888181651239734 : ((p5 ∨ (p1 ∧ (p3 ∨ ((((False → False) → p2) ∨ (((p5 → p5) ∨ p3) → (p1 ∧ (p5 ∨ (p2 ∨ p4))))) → (p3 ∨ False))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135302362059105995493207474302 : (((((p3 ∨ ((p5 ∧ p4) ∨ p3)) → (p2 ∨ (((True ∨ p2) ∨ p3) ∧ (p5 ∨ p3)))) ∨ p1) ∧ ((False → p1) ∨ p1)) ∨ ((p2 ∧ p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311229020786527179439241922564 : (p2 ∨ ((p2 → p1) → (((p2 → ((p3 ∨ ((p4 → ((False → (p1 ∨ False)) ∧ p5)) → p1)) ∨ (False ∧ ((False → p3) ∨ p5)))) ∧ True) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57406850106332199638647816867 : (((p1 ∨ (p2 ∧ p2)) ∨ (((False ∨ ((p4 ∨ (p1 ∨ ((p3 ∨ ((p4 → (p5 ∧ p5)) ∧ p4)) ∨ (p3 ∧ p4)))) ∨ True)) ∨ p2) ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_869332106754101874878294949 : ((p5 ∨ ((p4 → ((False ∧ (False ∨ (False ∧ p4))) ∧ ((p5 ∨ p3) ∧ (p5 ∨ p4)))) ∨ (p5 ∨ (True ∧ (False → (p2 ∨ p4)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227205703437892896639463666760 : (((True → p4) → p2) ∨ ((((p4 ∨ True) → p3) → (((True ∨ (((p4 ∨ True) → p1) ∧ p3)) ∧ ((p5 ∨ p1) → p4)) ∨ p3)) ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194664574078845320263187191230 : ((((p1 ∧ (False ∧ p1)) ∨ (p2 ∨ True)) ∨ p4) ∧ (p2 → ((p2 ∧ (((False ∧ (True → p3)) ∨ p2) ∨ ((p3 → (p2 ∧ p1)) → p5))) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300380702902262351135210450279 : (False ∨ ((((p5 → (True ∨ (p3 ∨ (False ∧ p2)))) ∧ ((False → p3) → (p1 ∨ p2))) → (((p4 ∧ p5) ∨ p1) ∨ p2)) ∨ ((p1 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68764510088417979372808376903 : ((p4 → (((p5 → (((True ∧ (p1 ∧ p5)) ∨ p4) ∧ (p2 ∨ p4))) → False) ∨ (False ∨ ((False ∧ (p3 ∧ True)) ∧ ((p4 → p3) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300997285476554568988411787754 : (False ∨ ((((False → (p2 ∨ p4)) → p5) → ((p1 ∨ (p5 ∧ True)) → p2)) → (p4 → ((True ∧ p3) → (((False ∨ (p5 → p1)) → p1) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351998086320917343975210515614 : (p4 → (((p3 → (p3 ∨ (p2 ∧ (p5 ∨ p2)))) → False) ∨ (((p1 ∨ p2) ∨ p4) → ((p5 ∧ (False ∨ p4)) → (p4 ∨ (False → (True ∨ p4))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149556661612152464173190706656 : ((p2 ∧ ((((p1 ∨ (p2 → False)) → p2) ∧ True) → ((p2 ∨ ((p3 → (p1 ∧ True)) ∧ (p4 → False))) → p1))) ∨ ((p3 ∨ (True ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347829385688338748343325205047 : (p3 → (((False ∨ p3) ∨ p3) → ((((((p5 ∨ p3) ∧ p1) ∧ p4) ∨ (p3 ∧ ((p2 → p2) ∨ p5))) → p2) ∨ ((False ∨ True) ∧ (p5 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198311193160443948962606155978 : ((p1 ∧ ((True → p2) ∨ (p4 ∧ (p1 ∨ p4)))) ∨ ((p4 ∨ (True ∨ ((True ∧ (p3 ∧ p1)) ∧ ((p5 ∨ ((False ∨ p2) ∨ p5)) → p1)))) ∨ p1)) := by
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
theorem thm_5_vars_118813060416256444438325595175 : ((True → (((((p2 ∨ p5) ∧ (p3 ∧ (True ∨ p5))) ∨ p4) ∧ (p3 → (((p2 ∧ (p3 → (True ∨ p2))) → p1) → p5))) ∨ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215560611301759303814758266323 : ((p5 ∧ ((p3 ∧ True) ∨ p4)) ∨ ((p2 ∨ (((p4 → ((p3 ∧ p3) ∨ p3)) ∧ (p5 ∨ ((p3 ∧ p5) ∧ p4))) ∨ (p4 ∧ p2))) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124333316902842353669753769452 : (((p4 ∨ ((((p3 ∨ True) ∧ p2) ∨ True) → True)) ∧ ((((p1 ∨ ((p1 ∨ True) → p3)) ∨ p5) ∨ (True ∨ p5)) ∧ (True → False))) → (p5 ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h10 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h11 := h6 h10
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h14 := h6 h13
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h28 := h23 h27
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h31 := h23 h30
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h36 := h23 h35
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69103770085688803185860938127 : ((p5 → (((((True → False) ∧ ((((p4 ∨ p1) ∨ p1) ∨ p1) ∧ p3)) ∧ ((p1 ∨ p4) ∨ (p2 → p3))) ∨ (p3 ∨ p3)) ∧ (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319750462239292121411904691409 : (p4 ∨ (((p4 → False) ∨ (p5 ∧ (p3 ∨ p5))) ∨ (((p4 ∧ ((p4 ∧ (p5 ∧ p2)) ∧ (p2 ∨ p4))) ∧ p3) ∨ ((False → p5) ∨ (p1 → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250099264617779240884441338682 : ((True → p4) ∨ (((p2 ∧ p4) ∧ (((False ∧ ((p3 → p4) ∨ False)) ∨ (p3 ∨ (p2 → p2))) → False)) ∨ ((True ∨ (p3 → p5)) ∨ (p2 ∨ p4)))) := by
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
theorem thm_5_vars_806300231918934843504003977737 : (((p4 → (((((p4 ∨ p3) ∧ p5) → p2) → (((((p2 → False) ∨ p4) ∨ (p5 → (p1 ∨ (p5 ∧ p2)))) ∨ p3) ∨ (p5 ∧ p4))) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_187328279902710870796284320665 : ((p2 ∧ (((p5 ∧ p4) ∧ (((p5 ∧ p3) ∧ p5) → True)) ∨ p4)) → (True ∧ ((False ∨ (p1 ∨ ((p1 ∨ True) ∨ (False → False)))) ∨ (p4 ∧ False)))) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257926361061966551545460224538 : ((p4 ∨ False) → ((p3 → (p2 ∨ ((((((p1 ∧ p5) ∨ p2) ∧ (True → (False ∧ ((p3 ∨ p3) ∨ p5)))) ∨ True) ∨ p1) ∨ False))) ∨ (True ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45548274734003146030927788773 : (((p2 ∨ ((((True → ((True ∧ (True → ((p3 → ((False ∧ p5) → (p5 ∨ (p3 ∧ p4)))) ∨ p2))) ∧ p2)) ∧ p3) → p4) → p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206511844888413600798554958965 : ((p5 ∨ (p1 ∨ (p3 → (True ∧ p5)))) ∨ (((p4 ∨ p5) ∧ False) ∨ ((p2 ∧ (((p3 ∧ False) ∧ False) ∧ True)) → (((p1 ∧ p1) ∧ False) ∨ p4)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587960270024554580052402617583 : ((((((p2 ∨ (((p5 ∧ p3) ∧ (False → (p1 ∧ p4))) → ((p1 ∧ (p2 → (p3 → True))) ∨ p4))) ∨ (p1 ∨ (p2 ∨ p3))) ∨ p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197774130515612895553207993444 : (((True → (p4 → p4)) ∧ (False ∨ (p1 ∨ p3))) ∨ ((p3 ∧ ((((True ∧ p4) ∧ (False ∨ True)) ∨ ((p5 ∧ p3) ∨ p1)) ∧ False)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355613278521892848857745794799 : (p5 → ((False ∧ ((((p4 → ((True → False) ∨ (p5 ∧ (p2 ∨ p3)))) ∨ True) ∧ p1) ∧ ((False → (p1 → (p2 ∧ p1))) → p1))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340151703593087908142821230004 : (p1 → (p4 → ((True ∧ (p4 ∧ ((p1 → (p4 ∧ p3)) ∧ (((((False ∧ p1) ∨ (p1 ∧ ((p3 → p1) ∧ p5))) ∧ p1) → p2) → p5)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337941607219925434007810897558 : (p1 → ((((p3 ∧ (p5 → (p1 ∨ p1))) ∧ ((p5 ∨ p4) ∨ False)) ∨ p5) ∨ (p5 ∨ (((p3 → p2) → ((False ∧ p5) ∨ (p4 → p2))) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48931260846642967644414443919 : ((((((p3 ∨ ((((False ∧ (False → p1)) ∧ p4) → p2) ∧ p5)) → ((p5 ∧ False) → p4)) → (p2 ∧ p2)) ∧ p1) ∨ ((True ∧ False) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_49009195394955905496407131986 : (((((((True → (True → p4)) ∧ ((p5 ∨ p2) → p2)) ∧ ((False → (p4 → (p4 ∨ p5))) ∨ p1)) ∨ p3) → p5) ∨ (p5 ∧ (True ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97603118312131302504248454102 : ((p3 ∨ (((p3 ∨ (False ∧ ((p2 → (True ∧ (p2 ∨ (p5 ∧ p2)))) → (False ∧ ((p5 ∨ True) → (p1 ∧ (p2 ∧ p2))))))) ∨ True) → p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∨ (False ∧ ((p2 → (True ∧ (p2 ∨ (p5 ∧ p2)))) → (False ∧ ((p5 ∨ True) → (p1 ∧ (p2 ∧ p2))))))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136311741001617198277356224084 : (((((p3 ∧ p2) → p5) ∨ p1) ∧ (((False → (True ∧ (True → p2))) ∧ ((((p5 → p1) ∨ p5) ∨ p3) ∧ False)) ∨ False)) ∨ ((p4 ∧ p5) → p4)) := by
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
theorem thm_5_vars_65640108349581049711230623978 : ((p4 ∨ (((True ∨ (((p1 ∧ p3) → False) → ((p2 ∨ p5) → False))) ∧ ((p3 ∧ (False → (False → True))) ∧ ((p1 ∧ p4) ∧ p1))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47528404793244997784133686326 : (((p4 ∨ (((p4 ∧ (((((p2 ∨ True) ∧ False) → p1) → ((p4 → (p3 ∧ (p1 → p2))) ∧ p1)) ∧ True)) ∨ True) ∨ False)) ∨ (p5 ∧ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_200739275557463209615722763618 : ((p3 ∧ ((p4 → True) ∧ ((p2 → False) ∧ p2))) → ((p1 ∧ p2) ∧ ((p5 ∧ (p5 → False)) ∨ (((False ∧ False) ∨ (p5 ∨ p4)) ∨ (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h22 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h23 := h20 h22
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717885867787454894627106734342 : (((((p1 ∨ (True ∨ True)) ∧ False) ∨ (True → ((((p5 → (p2 → True)) ∨ p4) → (((p3 ∧ p4) ∨ p2) → (p5 ∨ (p4 ∨ True)))) ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242549695269380721142412685137 : ((p3 → True) ∧ (((((p4 ∨ ((p5 ∧ (p4 ∧ True)) ∨ (p3 ∧ (p2 → p3)))) → p2) ∨ (p5 ∨ p1)) ∧ ((False ∧ p4) ∧ (p3 ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_618754255895537495494570294226 : ((((((p3 ∨ p5) → p5) ∧ (p2 ∧ (p5 ∨ ((p3 ∧ p4) → (((p2 ∧ (((p5 → (False → p3)) → p4) ∧ p4)) → False) → False))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_49536987036000767847415686549 : (((((((p1 ∧ True) ∨ ((p5 ∨ p1) ∨ ((p5 ∨ (p3 ∨ p2)) ∧ (p2 → True)))) ∧ p1) → p4) → (p4 ∧ True)) → ((p2 ∨ p5) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157740153230086345517838084111 : ((((p3 ∨ (((True ∨ (True ∧ False)) → (False ∧ False)) ∧ p5)) ∧ p4) ∧ ((False ∧ p1) ∨ (False ∧ p1))) ∨ ((True ∧ p3) ∨ ((False ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206355459345364923770223627270 : ((p2 ∨ ((p5 ∨ False) ∧ (False ∨ True))) ∨ (p4 ∨ (p3 → ((p1 → (p3 ∨ False)) ∨ ((p3 ∧ ((p4 ∨ p3) → p2)) → ((True ∧ True) ∧ p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190471780033936980414596901742 : ((((((False ∨ p4) ∨ p5) → (False ∧ p3)) ∧ p1) → p3) ∨ (((p5 → (p2 ∨ False)) ∧ ((p4 ∧ (p4 ∧ p4)) ∧ ((p5 → p2) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



