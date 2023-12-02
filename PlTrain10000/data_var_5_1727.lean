variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356473604214146051870795620727 : (p5 → (((p3 → ((p5 → p2) ∧ p3)) ∨ (p4 ∨ (p2 ∧ (p5 ∨ True)))) → ((p5 ∧ (p3 → (p2 → (p2 ∧ p3)))) ∧ (p3 ∨ (p2 ∨ True))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h11
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699100242704686446477322812070 : ((((p5 ∨ ((p5 ∨ (((p4 → p5) → (p4 ∧ p3)) → p2)) ∧ p4)) ∨ (((p2 ∧ (((p4 → p4) ∧ True) ∧ p2)) ∧ p1) ∨ (False → p1))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745160363438354649903667653383 : ((((p4 ∧ p5) → (((p5 ∨ (((p4 ∨ p5) → p2) → True)) ∧ (p2 ∨ ((((p4 ∨ (False ∨ p3)) ∧ p1) ∧ (p3 ∨ False)) ∧ p2))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213389193883977133424982562062 : (((False ∨ (p2 ∧ p3)) ∧ p4) ∨ (p1 → ((p2 ∧ (p1 ∨ (((((False ∨ (p3 → False)) ∧ p1) ∧ False) ∨ (True → False)) → p3))) → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198195090606747250999175231801 : (((p1 → p3) → ((p5 ∧ (p1 ∧ p2)) ∧ p4)) ∨ (p4 → ((p4 ∨ ((p2 ∧ ((p1 ∧ (p1 ∨ False)) ∧ (p5 → (p3 ∧ p2)))) → p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41615795964410713251094467601 : ((((p2 → ((((False ∨ p3) → p2) → True) → p1)) ∨ (p2 ∧ ((p3 ∧ (p2 ∨ p3)) → ((p1 → ((p4 → True) ∧ False)) ∨ p2)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135948633302676761933735377309 : (((((p5 → True) → (True ∨ p2)) ∧ (False ∧ (p4 ∨ p3))) ∧ (p5 ∨ (p4 → (((p5 ∨ (p1 ∧ p4)) → p5) ∧ p5)))) ∨ ((True ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24219651239507575948677880719 : (((p1 → ((p4 ∨ p2) ∧ p5)) → ((p2 ∧ p5) → ((True → ((((p4 → True) → p5) → (p3 ∨ p4)) ∧ False)) ∨ (p5 ∧ (True ∨ p3))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64483072261222951373564093244 : ((p1 ∨ (((True ∨ False) ∧ ((p2 ∧ (p1 → (p2 ∧ (False ∨ (False → (p5 ∨ True)))))) → (p3 → p1))) ∨ ((True ∨ p4) ∨ (p1 → False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_230491036124402412668506903921 : (((True → False) ∧ p4) → ((((p5 ∧ ((((((p1 ∨ p3) ∨ (False → True)) ∨ p3) ∨ ((p5 → False) → p2)) ∨ p3) → True)) → False) ∨ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60532279432421644780438375072 : ((True ∧ (((p1 ∨ (((((p1 → p5) ∨ p3) → (False ∧ (p4 ∧ (False ∧ True)))) ∧ ((p3 → True) ∨ p5)) ∧ p2)) ∨ (p5 ∧ p5)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57995566374031515071404825015 : (((p5 → (p4 ∨ False)) → (((((True ∧ p4) ∧ (p5 → p1)) → (((p5 ∨ True) ∧ p1) → ((False → p4) ∧ p2))) ∨ True) ∧ (p3 ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_322658987310897493180539485898 : (p5 ∨ (((p2 → ((p3 ∨ ((True ∨ p1) → (p3 ∧ (p3 → p2)))) ∧ (p5 ∧ ((p4 ∧ (p3 → (False → p2))) ∧ (p3 → p1))))) ∧ p2) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171489560103132678439941675448 : (((p1 → (p2 ∧ (p5 ∨ ((p5 → p3) → (((p5 → False) ∨ p3) ∧ p5))))) ∧ True) ∨ (p3 ∨ ((p5 → ((p4 → (p2 → p2)) ∨ p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119053816829345521895510785551 : ((p1 → ((True → (p3 ∨ (True ∧ (((False ∨ True) → (False → p1)) → (((p3 ∧ p1) ∧ False) ∧ ((False ∨ True) → p5)))))) ∨ True)) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338773909905497685429429510667 : (p1 → ((p2 ∧ p5) ∨ ((p2 ∧ (((p4 ∧ ((p2 → (False ∧ (p1 ∧ (p5 → True)))) ∧ p4)) ∧ (p5 → (p5 ∧ False))) ∨ False)) → (True ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114681876495922104136179470611 : (((p1 ∨ ((((True ∨ True) → p2) ∧ (p1 ∨ (True ∨ (p5 ∨ p4)))) ∨ (True ∧ p3))) ∨ ((False ∨ (p1 ∧ (p2 ∨ p2))) → p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38302015167940926261564593966 : ((((((p2 → p1) ∧ (((True ∨ p5) ∨ (p4 ∧ p1)) ∨ (((p2 → p4) ∨ True) ∨ p4))) ∨ p4) → ((p1 ∨ (p4 ∧ p4)) → p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179255959463030081018210935160 : ((p5 ∧ (p4 ∧ ((((p3 ∧ p3) ∨ p4) ∨ ((p1 ∨ p5) → p3)) ∧ p2))) ∨ (((((p5 → False) → True) ∧ (p4 → p5)) ∨ p1) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61343031894068317697220292250 : ((p1 ∧ (((False ∧ (p3 ∨ (((p3 → p1) ∧ (False → ((((p5 ∧ True) → p2) ∧ True) ∨ p5))) → (p2 ∨ p1)))) ∨ (p5 → False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358037287075020277152797576143 : (p5 → (p1 ∨ ((p2 ∨ (((((p4 → False) ∧ p4) ∧ (((p2 ∧ True) → p3) → (((False → p4) ∧ p2) ∧ (False → p5)))) ∨ p3) ∧ p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4234149469677653004000628890 : (p5 ∨ ((((p2 ∧ p1) → p3) → p1) ∨ ((((p3 → ((p4 ∨ (((True ∧ p1) ∧ p3) ∧ p1)) → (p4 → True))) ∨ p2) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325138160807826823269638894487 : (p5 ∨ (True ∧ ((((((False → True) ∧ (p2 ∧ p5)) ∨ p3) ∨ (p1 ∨ p2)) ∧ ((((False → p4) ∨ p5) ∨ (p5 ∨ p3)) ∨ p3)) ∨ (p5 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739613306856847717272683807375 : ((((p5 ∧ p4) ∨ ((((p1 ∨ (True ∨ ((p4 ∨ (False → (((p2 ∨ (p2 ∨ p2)) ∨ p2) ∧ p3))) → p1))) ∨ p3) → p5) ∨ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133650572125828716229964924112 : ((((p4 ∧ (((p2 → (p1 ∨ ((p1 ∨ p1) ∨ True))) ∨ p5) ∨ ((p2 ∨ p2) → (p4 ∧ p2)))) ∧ (p3 ∧ False)) ∧ False) ∨ (p2 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44108637400858505985947850385 : (((((((((p5 ∨ (p3 ∧ p2)) ∨ (p3 ∧ p2)) ∧ p2) ∧ ((p2 ∧ p3) → p4)) ∧ (True ∧ False)) → True) ∨ ((True → p4) ∧ p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995597949372421569964269092396 : (((p5 ∧ (((p4 ∧ p5) → p4) → ((p5 → ((((((p3 ∧ p4) ∧ True) → p1) ∧ True) ∧ (p1 ∧ p2)) ∧ False)) ∧ (p2 ∧ (p3 → False))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ p5) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696043178730102226367130824359 : ((((p3 ∧ ((((p3 ∨ (p2 ∧ (p5 ∨ True))) ∨ False) ∨ (p1 ∨ False)) ∧ p2)) → ((True ∧ ((p3 → (p4 → p1)) ∧ (p5 ∨ p1))) ∨ p3)) ∨ p4) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219147015526171813465337168888 : ((True ∨ (p3 → (p3 ∧ p2))) → ((((p4 ∧ (p4 ∧ (p4 ∨ p3))) ∨ (p5 ∨ ((p3 ∨ (p4 ∧ p5)) ∨ p1))) ∧ p1) → ((False ∧ p5) ∨ True))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
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
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173459760674692391845575649339 : (((((p2 → (True ∧ (p5 ∧ ((p3 ∨ (False ∧ p1)) → p4)))) ∨ p3) ∨ p1) ∧ p1) → (p4 → (((p4 ∨ (p1 ∨ (p4 ∨ p2))) ∧ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769746497418412922874735839276 : (((p5 ∧ (p2 ∨ ((p3 ∨ p2) ∧ (((((p5 → p4) ∧ p2) ∧ ((p1 → p2) ∧ p1)) → (p2 → (((p3 ∨ p2) ∧ False) ∨ p3))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137446403298751551282855432376 : ((p4 ∧ (((False → ((p4 ∧ p3) ∧ True)) ∧ True) ∧ ((p1 ∧ ((p5 → (p4 ∨ True)) → p4)) ∧ ((p4 → p3) → p1)))) ∨ ((p2 ∧ True) → p2)) := by
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
theorem thm_5_vars_113763727839180614421471632771 : (((((p2 ∧ (p3 → p4)) → (p2 ∧ True)) ∨ ((p1 ∧ (p5 ∨ ((p4 → p1) ∧ p3))) ∧ ((p2 ∧ True) → False))) → (p3 ∨ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135241556760658918891410211855 : (((((p2 ∧ p3) → p5) → ((((p4 ∧ p3) → False) ∧ ((p3 → p2) ∧ p5)) ∨ ((p2 ∨ False) ∨ p3))) → (p2 → p5)) ∨ (False ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224689773795693584523327315528 : ((p3 → (p5 ∨ True)) ∧ ((((p4 → False) ∧ (p4 ∧ (((p5 ∧ p2) ∧ (False → p1)) ∨ ((False → p2) ∧ p1)))) ∧ (p4 ∧ p5)) → (p1 ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h4.left
    let h15 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h16
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h24.left
    let h35 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h33
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h24.left
    let h40 := h24.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h41 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h39
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h42 := h25 h41
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158395498765850207285805634721 : (((p4 → True) ∧ (p2 ∨ (p4 → ((((False ∨ (p2 ∧ (p1 ∧ True))) ∨ True) → p1) ∧ (p5 ∨ p1))))) ∨ ((p4 → (p5 ∨ p3)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114635099944883033564942621646 : (((((((p5 ∨ ((p5 ∧ False) ∨ p4)) → (False ∨ False)) ∨ (p1 ∨ p4)) → p3) → p4) ∨ ((p3 → (p5 → (False ∧ p4))) ∨ p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16778635425879098884808941294 : (((((p5 → (((True ∨ (True ∨ True)) → True) → p3)) ∨ p2) ∨ (((True → (False ∧ p1)) ∨ p4) ∨ (True ∧ False))) ∨ (p2 ∨ (p4 → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54095478561812114522969765808 : ((((p1 → p3) → (p1 ∨ (((p1 ∧ p1) ∨ p5) → p3))) → ((((True ∧ p2) → ((((p3 → True) → p3) → p1) ∨ p1)) ∧ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90920012482177736245162812594 : (((True → False) ∧ ((((False → ((p4 ∧ p2) → p1)) → p4) ∧ ((p3 ∧ (p3 ∨ (p1 → ((p4 ∨ False) ∧ p3)))) → False)) ∨ (p2 → p4))) → p3) := by
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
theorem thm_5_vars_184106612529164727090252805053 : ((((False ∧ True) ∨ ((p5 → (p1 ∧ (True ∨ p1))) → p2)) ∨ p3) ∨ ((p1 → (True → False)) → (p3 ∨ (True → (True → ((p1 → p5) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599498192061937352411058016255 : (((((p1 ∨ p3) ∨ (p1 ∨ (((False ∨ False) ∨ False) ∨ ((((p5 ∨ p1) ∨ (((False ∨ True) ∧ p5) ∨ (True ∧ False))) → p4) ∨ p2)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190576343140447446395431804360 : ((((False → (p2 ∨ p3)) ∨ (False ∧ (p5 ∧ True))) → False) ∨ ((((p3 ∨ ((p3 ∧ False) ∨ (False → ((p1 ∧ p4) → True)))) ∨ p5) ∨ p2) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172459917354443685585522151646 : (((p5 ∧ (p2 ∨ (p2 ∨ p1))) ∨ (((p2 ∧ True) ∧ (p3 → p1)) ∨ (p2 ∧ False))) ∨ ((False ∧ True) → (p5 → ((p1 ∨ (False ∨ p4)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58242153435067711035419923276 : (((p5 ∧ False) ∧ ((((((p5 → p1) ∧ p3) → ((((p4 → (p5 ∧ p5)) → p1) ∧ True) ∧ (False ∧ True))) → p3) ∨ (False → False)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322414230291274059728268814751 : (p5 ∨ (((p5 ∧ ((((True ∧ p4) → p3) ∧ (p4 ∨ p5)) ∨ p2)) ∨ (False → ((False ∧ p5) → (p1 ∨ (p2 ∨ ((False ∧ False) → p1)))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192781323333167994555489749020 : (((True ∨ ((p5 ∨ p3) → (p2 ∧ (p4 → False)))) → False) → ((((p4 ∨ (p2 ∨ p5)) → ((p5 ∧ ((p2 ∧ p5) ∨ p2)) ∧ False)) ∨ p3) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p5 ∨ p3) → (p2 ∧ (p4 → False)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((p5 ∨ p3) → (p2 ∧ (p4 → False)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51534548517622368175096285194 : (((True ∧ (True ∧ ((p2 → ((p2 → p3) → True)) → (((p4 ∨ p1) ∨ False) ∧ (True ∨ p1))))) → ((p2 ∨ p5) ∨ (p2 → (True ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133912756435940112212458604433 : (((p3 ∨ ((((p1 ∧ True) ∧ (p5 ∨ (p2 ∨ ((p3 ∧ p2) ∨ True)))) ∧ (p1 ∧ (True ∨ p2))) → (False ∧ p3))) ∧ p3) ∨ (False → (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701627244720355119940083298086 : (((((p3 ∨ p4) ∨ (((True ∧ p3) → (p3 ∧ p4)) ∨ p4)) ∧ (((True ∧ p2) ∨ ((True → p2) ∧ ((p2 ∨ p5) ∧ p3))) ∧ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2783512847909616101013754601 : (((p3 ∨ True) ∧ (p5 ∧ p5)) ∨ ((True ∧ (p4 ∧ p2)) ∨ (True ∨ (((((False ∧ p2) ∨ p2) → p3) ∨ (False ∧ (p4 ∧ p3))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139832972566704387803636912994 : (((p1 → (p1 → (p2 ∨ (True ∨ ((p5 ∨ (((p1 ∧ True) → (False ∧ p2)) → (p1 ∨ True))) → (False → p3)))))) → p5) → (p4 ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p1 → (p2 ∨ (True ∨ ((p5 ∨ (((p1 ∧ True) → (False ∧ p2)) → (p1 ∨ True))) → (False → p3)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62708456398697198528911675357 : ((p4 ∧ ((((True → False) ∨ p1) ∨ (p5 ∨ (p5 → ((((p5 ∧ p1) ∧ ((p4 ∧ p2) ∨ (p3 ∧ p5))) ∨ (p2 → True)) → p1)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587933953164836538522767312612 : ((((((p2 → (((p1 ∨ ((((p4 ∨ p5) → p3) ∨ False) ∧ p1)) ∨ p1) ∧ ((p3 → p1) → p1))) ∧ ((p2 ∨ p3) → p3)) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319547400799527199381211774924 : (p4 ∨ ((((p2 ∧ False) ∧ (p3 ∧ p5)) ∨ (p3 → (p1 → True))) ∨ (True → (p1 ∧ (p1 ∨ ((False → ((True → (p3 ∨ True)) → p4)) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142197154247630199342738996192 : ((p1 ∧ (((p1 ∨ ((True ∨ p4) ∨ ((p3 → p3) ∧ (p1 ∨ True)))) ∧ ((p1 ∨ p1) ∨ p3)) ∧ ((False → p4) ∧ p5))) → (p3 ∨ (p4 ∨ p1))) := by
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
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h5.left
        let h12 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h5.left
        let h15 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h5.left
            let h25 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h5.left
            let h28 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h5.left
          let h31 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h5.left
            let h36 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h5.left
            let h39 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h5.left
          let h42 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h40
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h47 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h48 =>
            -- Conjunctions on the left can always be decomposed.
            let h49 := h5.left
            let h50 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h51 =>
            -- Conjunctions on the left can always be decomposed.
            let h52 := h5.left
            let h53 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h51
        case inr h54 =>
          -- Conjunctions on the left can always be decomposed.
          let h55 := h5.left
          let h56 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h54
      case inr h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h58 =>
          -- Disjunctions on the left can always be decomposed.
          cases h58
          case inl h59 =>
            -- Conjunctions on the left can always be decomposed.
            let h60 := h5.left
            let h61 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h59
          case inr h62 =>
            -- Conjunctions on the left can always be decomposed.
            let h63 := h5.left
            let h64 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h62
        case inr h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h5.left
          let h67 := h5.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748006438087218426353740344716 : ((((p1 → False) → ((False ∧ (True → (False ∨ (p3 → p2)))) ∧ (p5 ∧ (p4 ∨ ((p3 ∧ (((p4 ∧ p2) ∧ p1) → p2)) ∨ (p5 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38969919680025519030457402714 : ((((False ∧ p3) ∧ (p4 → (p5 ∧ ((p4 ∨ (p1 ∧ p3)) → ((p5 ∧ p2) ∧ ((False ∨ (p4 ∧ ((p4 ∧ p4) ∨ p3))) → False)))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60209381163793944183474359826 : (((True → True) → (p3 ∨ ((True ∧ p4) → ((((True ∧ p1) ∨ (((p5 ∧ p2) ∧ p4) → p5)) ∨ (True → (p2 ∨ p1))) ∧ (p5 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914185343168148161167820533281 : (((((True ∨ (p4 ∨ (p2 ∨ ((True ∧ p1) ∧ (p1 → ((p4 → p4) ∨ p4)))))) → p2) ∧ ((p2 → ((p2 ∨ True) ∧ (p1 ∧ p5))) ∨ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p4 ∨ (p2 ∨ ((True ∧ p1) ∧ (p1 → ((p4 → p4) ∨ p4)))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136169099977415837873401416983 : ((((((p3 ∨ p3) ∨ p3) ∨ p4) ∧ True) ∧ (p1 ∨ ((((False → p1) ∨ p4) → p5) → (((p2 ∧ False) → True) ∨ p3)))) ∨ (p4 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113627068259017977439439909947 : (((p2 → ((((p4 → False) ∨ (p1 ∧ (p2 → ((((p5 ∧ p3) ∨ p3) ∨ p2) ∧ p4)))) ∨ True) ∨ (p1 ∨ p5))) ∨ (p2 ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58707323592858021223871403675 : (((p2 → p5) ∧ (p1 ∧ ((((p4 → p3) ∨ False) ∨ p4) ∧ (p5 ∨ ((True → ((p2 → p1) ∧ p4)) ∧ (True ∧ (p5 ∨ (False ∧ False)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165320608625157336628344540296 : (((p3 → (p1 ∨ (False → (p5 ∧ (p5 → ((p3 ∨ p3) ∧ (p2 ∧ True))))))) → (p5 ∨ p4)) ∨ ((p3 ∨ p5) ∨ (p2 ∨ ((False → p4) ∨ p4)))) := by
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
theorem thm_5_vars_606206867759013869525915518361 : ((((((((((p1 ∧ (p5 → False)) ∧ True) → True) ∧ p4) ∨ (((p4 → False) → p4) → (((p4 ∧ p5) ∨ True) ∧ p5))) ∧ p3) ∧ p5) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134044348244612982266652474006 : (((((p4 ∧ p5) ∧ (p2 ∧ (((p4 ∧ (p4 ∨ p2)) ∧ p1) ∨ (p5 ∨ ((p2 ∨ p3) ∧ (False ∨ False)))))) ∨ True) ∨ p4) ∨ ((p4 → p3) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48974089123525384483090135862 : (((((p4 ∧ (p5 ∧ ((True ∨ (p3 ∧ ((p4 ∧ ((p4 → p2) → True)) ∧ p1))) ∧ p1))) ∨ (p1 ∧ p1)) ∨ p4) ∨ ((True ∨ True) ∨ False)) ∨ p4) := by
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
theorem thm_5_vars_17917949134640352120145659599 : ((((p5 ∨ (False ∨ (False ∧ (((p4 ∨ False) → ((p5 ∨ (p1 ∧ p1)) → p3)) ∧ p2)))) ∨ (p3 ∧ p4)) ∨ (False → (p4 → (p3 ∧ p2)))) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41065969685204561584608675503 : ((((True ∨ (p1 ∧ (True → (((((((p1 ∧ p1) ∨ p1) → p5) → p1) ∨ p1) ∨ p1) ∧ ((False → p2) ∨ p3))))) → (p2 ∨ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161426546699986327021063965218 : ((p2 ∧ (((((p2 → p4) → False) ∨ False) ∨ ((p2 → True) ∧ (p1 ∨ (False → False)))) → (p5 ∨ False))) → (((True ∧ p2) → (p5 → p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 → p4) → False) ∨ False) ∨ ((p2 → True) ∧ (p1 ∨ (False → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196767453285964535802778388891 : (((((True ∧ False) → False) → (p5 → p1)) ∧ p5) ∨ ((True → ((p3 → p2) ∧ False)) → (False ∧ (p4 → ((((p4 → p3) ∧ p4) → p3) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51739472036433259628377618021 : ((((p2 → (False ∨ p4)) ∧ (((p4 → (True → True)) ∧ ((True → p4) ∨ True)) ∧ p2)) ∧ (((True → (p3 → p5)) ∨ (p1 ∧ p2)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41162200332023183970178021799 : ((((p5 ∨ ((((((p4 → p5) → p5) ∧ (p5 ∨ (p3 ∧ ((p1 → p5) ∨ True)))) ∨ True) → p5) ∧ p5)) ∨ (p3 ∨ (p2 ∧ p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39443177786322971900619342627 : (((p5 ∧ ((p3 ∨ (p2 ∧ ((p3 ∧ (((((False ∨ True) → p3) ∧ p4) ∨ (p5 ∨ p1)) ∨ p1)) ∨ (p1 ∨ p4)))) ∧ (p3 ∧ p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187094085839711473654081618821 : (((p4 → False) ∧ (p4 ∧ (p2 → (((p2 ∨ p5) → p1) ∨ False)))) → (((p4 → (p4 ∨ (True ∨ (((p2 ∨ False) ∨ False) → False)))) → p2) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53163769790102921352862629934 : ((((p5 ∨ (((p5 → (p4 → False)) → p4) ∧ (p4 ∨ p3))) ∨ p5) ∨ ((((p2 ∨ p4) ∧ (p5 → ((p4 → p3) ∨ p4))) → p3) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156647123344905613255750884424 : ((((((p3 ∨ ((p4 ∧ (((True ∧ p1) ∧ p3) ∨ (p2 ∨ p1))) → p4)) ∧ p1) → p5) → p1) ∧ p5) ∨ ((((True ∨ p4) → False) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53863378441830335509978702091 : ((((p2 ∨ (p2 ∨ p5)) → ((p4 ∧ p2) ∧ (False ∧ p2))) ∨ (((((p4 ∧ p5) ∨ p1) ∨ ((p3 ∧ False) → True)) → (p2 → True)) ∨ p2)) ∨ p4) := by
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
theorem thm_5_vars_227364869848224600535861809617 : (((p3 → p4) → p4) ∨ ((p3 ∨ (((False ∧ p5) ∧ p3) ∨ ((p1 → True) → (True ∧ (p4 → p4))))) → ((p1 ∧ p2) ∨ ((p2 ∧ p3) → p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257637908255190305539095373807 : ((p3 ∨ p2) → ((p3 → (p1 ∨ (p2 → p3))) ∧ ((p4 → ((p3 ∨ False) → (False ∨ True))) ∧ (p4 ∨ ((p4 ∧ (p1 → p3)) ∨ (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
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
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190270051170053279955903102210 : ((((((p4 ∨ p3) → True) → (p1 ∨ p3)) ∨ True) ∨ True) ∨ ((True → ((p2 ∨ p2) ∧ (p3 → p5))) → (p3 ∧ (False → (True → (p2 ∧ p4)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56645199167362441571635549556 : ((((p1 ∨ False) ∧ False) ∧ (((False ∧ (p3 ∨ (p5 ∨ (((((p3 → p1) → p5) ∧ False) → p5) → p5)))) → p1) ∧ (p5 ∨ (p2 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65557239666401630371086656920 : ((p3 ∨ (p1 → (True ∧ (((p3 ∧ ((p2 ∧ p2) ∨ p3)) ∨ ((((p2 → ((p2 → True) → p1)) ∧ True) ∧ False) ∨ p5)) ∨ (p4 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84130690937385585934197332805 : (((True ∧ ((((p1 ∧ ((p3 ∨ False) → p5)) → p3) → p4) ∧ ((p3 ∨ p1) ∧ p3))) ∧ ((p1 ∨ (p1 ∧ p3)) → ((p3 ∧ p2) ∧ p4))) → p4) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : ((p1 ∧ ((p3 ∨ False) → p5)) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h11
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ (p1 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174489052381903509594581672161 : (((p1 → ((p1 ∧ p3) ∧ (p5 → p1))) ∧ ((((False → p3) ∨ p3) ∧ p3) ∨ p2)) → (((p2 ∨ (False ∨ (p3 → p3))) ∧ p5) ∨ (False → p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37347149771043845193006554316 : (((((p5 → (p1 → ((p4 ∧ (False ∨ ((p4 ∨ p1) → (False → True)))) → ((p4 ∧ p2) → ((p1 → p3) ∧ False))))) ∧ p1) ∨ p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613996408505892098793746655869 : ((((((False ∨ (True ∧ (False → p1))) ∧ (p4 ∨ (((p4 ∧ (((p4 → p4) → p4) → p4)) ∧ p1) → p2))) ∨ (False → (p5 ∨ p1))) ∨ p2) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_984071660837985366872818602779 : (((p1 ∧ (p2 ∧ (((((p1 ∨ p4) ∧ (True → False)) ∧ (p1 → (((((p1 → False) ∧ p2) → p2) → (p1 → False)) → True))) ∧ p2) ∧ p5))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
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
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979588284554862427334568137 : (True → ((((False ∨ ((p5 ∧ (p4 ∧ p5)) ∧ ((p4 → (p4 ∨ True)) → p5))) → ((False ∧ (p1 ∨ True)) ∧ p1)) ∨ ((p3 ∧ True) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336138967517856041493453158610 : (p1 → (((p2 ∨ (p5 → (p3 → ((False → True) → (((p1 ∧ (True ∧ ((p4 ∧ p4) ∧ p1))) ∨ p4) ∧ ((True ∧ p4) → p5)))))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338966146738745497543347832045 : (p1 → ((p2 → True) → ((False → p5) ∧ (((p2 → (((p5 ∧ p3) ∧ p5) ∨ (((p1 ∧ (p4 ∧ p4)) ∨ (p4 → True)) ∧ p2))) ∧ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187724829826443639560338643392 : ((p1 → ((p1 ∨ (p2 ∨ ((p5 ∨ p5) → True))) ∨ (p1 ∨ p2))) → (((p1 → p5) ∧ (((True ∨ False) ∧ (p5 ∧ p3)) ∧ False)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147892687310263730124815244264 : (((((p5 ∨ (((p4 ∨ p5) → p2) → (p1 ∨ ((p5 → (p4 ∧ p5)) ∨ False)))) ∨ True) ∨ p1) ∧ (p1 → p4)) ∨ (((p2 ∧ p4) → p2) ∨ p5)) := by
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
theorem thm_5_vars_266058531590006116865809753403 : (True ∧ (p2 → (((((((p1 ∨ p1) ∨ p1) ∧ (True ∨ ((False → (p1 → p4)) ∨ ((p3 → p2) ∧ (p4 → p2))))) ∧ p1) → p2) → False) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233749140402171863256752210669 : ((p3 ∨ (True ∨ True)) → (p5 → ((((p2 → (p5 → True)) → (False ∧ ((False → p5) → ((p3 ∧ True) ∨ False)))) → (p2 ∧ p3)) ∧ (p5 ∨ p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (p5 → True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h5
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p2 → (p5 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h12
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : (p2 → (p5 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h18
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : (p2 → (p5 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h29 := h3 h26
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h32 : (p2 → (p5 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h33
        -- Implications on the right can always be decomposed.
        intro h34
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h35 := h3 h32
      -- We need to get the left conjuct of h35 based on <expert-advice>.
      let h36 := h35.left
      -- False on the left can always be used.
      apply False.elim h36
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h37 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h40 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218465030795146847309257900991 : (((p5 ∧ p4) → (False ∧ p1)) → ((((False ∨ p1) ∧ ((((True → p2) → (p4 ∨ p4)) ∨ p5) ∨ ((p5 ∨ (p4 ∧ p5)) ∧ p2))) ∧ p2) → p1)) := by
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
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662659726092684084194086492143 : (((((p5 ∨ (False ∨ (p3 → p4))) ∧ ((p1 → (False ∨ (False → p3))) ∨ ((p3 ∨ p1) ∧ ((p2 → (p3 ∨ True)) ∧ p5)))) → (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697985102917905580109405379544 : (((((((((True → p3) ∧ p5) ∧ p2) ∧ (p2 ∧ False)) ∧ p1) ∨ p2) ∨ ((p5 → (True ∨ True)) ∨ (False → ((False ∨ (True → p4)) → p1)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113271175937119933475754380694 : (((((((p5 ∧ p3) ∧ (((True → p4) ∧ p5) → True)) ∧ (p2 ∧ p3)) → p2) ∧ ((p1 ∧ (p2 ∧ p1)) ∧ p5)) ∧ (p5 → p1)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207545540556845534400538551237 : ((((p5 → (p1 ∧ p4)) ∧ p4) → p1) → (p2 ∨ ((((p4 ∨ p4) ∧ (p2 → (False ∨ False))) ∧ ((p1 → (p2 → (p5 ∧ p4))) ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



