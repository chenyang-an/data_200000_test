variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166273980818358416615595452665 : ((p3 ∧ (p1 → ((p4 → p3) ∨ (((p3 → True) ∨ p2) → (((p2 ∨ p5) ∨ p3) ∧ True))))) ∨ (((p1 ∧ (True → p1)) ∨ (p5 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651311646003160131034251797206 : ((((((p2 ∧ True) ∧ False) ∨ ((False → (((p5 ∧ (False → p3)) ∧ p3) → (True ∨ True))) ∧ (p1 ∧ (p5 → (p4 ∨ p4))))) ∧ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150162137415346843834741777769 : ((p1 → (((False ∨ ((p5 ∧ (p5 ∨ p4)) ∨ True)) ∧ p5) ∨ ((p4 → (p3 ∧ (p3 ∧ p3))) ∨ (p2 → True)))) ∨ (p5 → (p2 ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301868401735296606447613873420 : (False ∨ ((p2 → p5) ∨ ((p1 ∨ (p5 ∨ (p4 ∨ (True ∧ (p5 → p4))))) → (p4 → (p5 → (((p2 ∨ (p1 → (p4 ∨ p1))) ∨ p3) ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646374643328735522083802610362 : ((((False → (True → (((p5 → True) ∨ p3) ∨ (p1 ∧ ((p5 → (((p4 ∧ p5) ∨ ((p4 → p2) ∧ (False → False))) ∧ True)) ∨ p3))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614039762579260166597880890731 : ((((((False ∨ p1) → (p4 ∧ (p4 ∨ ((((True ∨ False) ∨ True) → (True ∧ (True ∧ (p5 → p2)))) ∨ p3)))) ∨ (p3 ∨ (p2 → p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312314864116584315760324684143 : (p2 ∨ (p2 → ((((True ∧ (p2 ∨ p3)) → (True → False)) ∨ p5) → (p2 ∧ (((p1 → ((p3 ∧ p1) ∧ (True ∧ False))) → (p3 → p4)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168542326066439349421711786679 : ((p1 ∧ ((p1 ∨ ((p2 ∧ ((False ∧ p4) ∨ p3)) ∨ (((p1 → p2) → p3) ∧ False))) → p5)) → (((p1 → p2) ∧ (p3 ∨ p4)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263122639665991106393792806696 : (True ∧ (((p2 → ((((p1 → (p4 ∧ p2)) ∧ (p3 ∨ True)) ∧ p5) ∧ False)) → (p4 ∨ ((p1 ∨ (p5 → p2)) ∨ (p5 ∨ p4)))) ∨ (False → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113461368393688472758051059345 : ((((((p3 → ((p4 ∧ p4) ∨ p3)) → (p3 ∨ p2)) ∧ ((((True ∨ p1) ∨ p2) ∧ (True ∧ p1)) ∨ True)) → False) ∨ (False → False)) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356194027934798209892196857486 : (p5 → (((p3 ∧ (p1 ∧ ((p4 ∧ (p1 ∨ p5)) → False))) → (((p2 → False) ∧ (p5 → True)) ∨ p3)) → ((True → (p2 ∨ p3)) ∨ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113265732017516088245533627261 : (((((p2 ∨ p1) ∨ (((p3 → (p4 ∨ p3)) ∨ False) ∧ (p4 ∨ (True ∧ (p4 → p2))))) ∨ ((p2 ∧ p1) ∨ p5)) ∧ (p2 → p5)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44971609743387880589431007958 : ((((False → p1) ∧ ((p1 ∧ (True → p5)) ∧ ((p4 ∨ ((((p3 ∧ True) → True) → (False ∨ ((p1 ∨ p3) → True))) ∧ p2)) ∨ p5))) → p1) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318580690200548030722207180597 : (p4 ∨ (((p1 → ((((p5 ∨ ((p3 ∨ p5) → ((False ∨ p5) → p2))) ∨ (p3 ∧ (p1 ∧ p3))) ∧ p4) ∨ p4)) ∨ (p1 → p2)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89245213849150201225723496477 : (((p2 ∧ (True → p5)) ∧ (p4 ∨ ((p3 → (((p5 → p4) ∧ p1) → (p4 ∨ p3))) ∨ ((True ∨ True) → ((True ∨ (p4 ∧ p4)) → p5))))) → p5) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218266596772677795483825464232 : (((p1 ∨ p4) ∨ (True ∧ p3)) → ((p3 ∨ (((True ∧ True) → False) ∧ ((True ∧ p2) ∨ True))) ∨ ((False ∧ True) → ((False → (p1 ∧ p1)) ∨ p3)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134364976371256719264053607749 : (((p1 ∨ ((p3 ∧ p5) ∧ ((p3 → ((True → (True ∧ ((((p4 ∧ p3) → True) ∧ True) ∧ False))) ∧ p2)) → p5))) ∨ p4) ∨ (p4 → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173969574045394371845067964185 : ((((False → (p2 → (True → True))) → ((p2 ∧ p1) ∨ ((False ∧ p4) ∧ p2))) → p3) → (((p3 ∨ p4) → False) → (True → ((p3 → p4) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211641725328506875269614115954 : (((p2 → p3) → (True ∨ p2)) ∧ ((((True ∧ ((p3 → (p1 ∨ ((p2 → ((p2 ∧ False) → p2)) → p4))) → True)) → p4) ∨ p3) ∨ (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_147430680411278100483350768050 : (((((False → False) ∨ p1) → ((((p5 ∨ p3) → (p2 → (p5 ∨ ((True ∧ p1) ∨ p1)))) ∧ p3) → p4)) ∨ p1) ∨ (p2 ∨ ((True ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695320119624688443514298334406 : ((((((p5 → p1) ∨ (((p4 ∨ (p5 ∨ p3)) ∧ (p1 ∨ p3)) ∧ p2)) → p2) → (False ∨ (p3 → ((p5 ∧ p3) → (p4 ∧ (p1 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65468678868055526416804196651 : ((p3 ∨ (True ∧ (p4 → (((p1 ∧ (p3 ∧ (p3 ∧ (((p4 ∨ (p5 ∨ p5)) ∨ p5) ∨ (p2 ∧ ((p4 ∧ p4) ∨ False)))))) → p2) ∨ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_686161927067130948960051024499 : (((((p4 ∨ (p2 ∨ ((p5 ∨ (True ∧ (False → p5))) ∨ (p3 → p3)))) → (False ∧ (p5 → False))) → (((p2 ∨ True) → p3) ∨ (p5 → False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (p2 ∨ ((p5 ∨ (True ∧ (False → p5))) ∨ (p3 → p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667226943402416534647823239297 : (((((True ∨ False) ∧ (((p5 ∨ ((True → (p5 → True)) → p2)) ∧ ((p2 ∧ True) → (p4 ∨ (p2 ∧ p4)))) ∧ False)) ∧ ((p2 ∧ p5) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312279163403944272544046835953 : (p2 ∨ (p1 → (p2 → ((p3 → ((p4 → ((((p1 ∨ (p4 → p1)) ∨ p5) ∧ ((p4 ∧ p2) ∨ (p1 → True))) → (p3 ∧ p5))) ∧ p3)) ∨ p1)))) := by
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
theorem thm_5_vars_59157012085816694648061217958 : (((False ∨ p1) ∨ (True ∧ ((p4 → (True → (((((False → (p3 → False)) ∧ True) ∨ p3) → p2) → (p2 ∨ p3)))) → (False ∨ (p5 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134866596420055783745804749817 : (((False → (p2 ∨ (((((((p4 ∧ p3) ∧ p1) ∧ p1) ∧ p1) ∧ p3) → (p5 ∨ (False ∨ p1))) ∧ (p1 → p3)))) → p3) ∨ (False ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7699963110958683985413995617 : (((((((p5 ∨ (p4 → p1)) ∨ (p5 → p3)) ∨ ((((p1 ∨ (p4 ∨ p5)) ∨ (False ∨ (True → p1))) → p4) ∧ p3)) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731856362671122502404126009761 : ((((p4 → (p4 ∨ p2)) → (((p5 ∧ (((p2 → False) ∧ (p5 ∨ ((p4 ∧ True) ∨ True))) → (False ∧ (p1 → False)))) ∨ True) ∨ (p5 → p3))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161549579355732984262394224808 : ((p5 ∧ ((p5 → False) ∧ ((p5 ∨ (((True ∧ p4) ∨ True) ∨ ((p5 ∧ p1) → p5))) ∨ (p4 → p2)))) → (p3 ∧ ((p4 ∨ p4) ∧ (p3 ∨ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h15 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h16 := h4 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h19 := h4 h18
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h22 := h4 h21
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h24 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h25 := h4 h24
    -- False on the left can always be used.
    apply False.elim h25
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
      have h32 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h28, we can now drive its conclusion.
      let h33 := h28 h32
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h40 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h41 := h28 h40
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h43 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h44 := h28 h43
        -- False on the left can always be used.
        apply False.elim h44
  case inr h45 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h46 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h47 := h28 h46
    -- False on the left can always be used.
    apply False.elim h47
  -- Conjunctions on the left can always be decomposed.
  let h48 := h1.left
  let h49 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h50 := h49.left
  let h51 := h49.right
  -- Disjunctions on the left can always be decomposed.
  cases h51
  case inl h52 =>
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
      have h54 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h53
      -- We have shown the premise of h50, we can now drive its conclusion.
      let h55 := h50 h54
      -- False on the left can always be used.
      apply False.elim h55
    case inr h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h60
        case inr h61 =>
          -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
          have h62 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h48
          -- We have shown the premise of h50, we can now drive its conclusion.
          let h63 := h50 h62
          -- False on the left can always be used.
          apply False.elim h63
      case inr h64 =>
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h65 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h48
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h66 := h50 h65
        -- False on the left can always be used.
        apply False.elim h66
  case inr h67 =>
    -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
    have h68 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h48
    -- We have shown the premise of h50, we can now drive its conclusion.
    let h69 := h50 h68
    -- False on the left can always be used.
    apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616897337482609259380783902080 : ((((((p4 ∨ (p5 → (p3 ∧ False))) → ((p3 ∨ p5) ∧ p4)) → ((((((p2 ∧ (p3 → p5)) → p3) → True) ∨ p4) → False) ∨ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17234012780902023825967411219 : ((((((((False ∨ True) ∧ p3) ∨ p3) ∨ p3) ∨ (p2 ∨ (False → p1))) → ((p5 ∧ (p3 ∨ (p3 ∧ p4))) ∨ p1)) → (p5 → (p1 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112154918290089608564852396899 : (((p2 ∧ (((True ∨ (((p5 → p4) ∧ (p1 → p4)) → False)) → (p1 ∨ (p4 → (p3 ∨ p4)))) ∨ (p2 ∧ (p2 → p4)))) ∨ True) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50305497979183210846346622192 : (((((p2 → ((((p1 ∨ False) ∧ (False → p5)) ∧ p1) → False)) ∧ p3) ∧ (p2 ∧ (p2 ∨ (True ∧ p1)))) ∨ ((p4 → (False ∧ p4)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147604854702459918595086881577 : (((((p4 ∧ (False → p5)) ∨ ((((p2 ∨ p1) ∧ p2) ∧ p2) → (p4 → ((p3 ∧ p3) ∨ p1)))) ∨ p3) → p3) ∨ (((p2 ∨ p5) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688979310636191668893282234682 : ((((((p5 → (((True → p4) ∧ (p1 ∨ (True ∨ p4))) ∧ (p1 ∨ p3))) ∧ p2) ∨ False) ∨ ((False ∧ p2) → (False ∧ (p5 ∨ (p4 ∧ p3))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114292643987922351025047063356 : (((((True → ((((p4 → p3) ∨ p2) ∨ (p3 ∨ (p3 → p2))) ∨ p3)) ∨ p2) ∨ (p5 ∧ p3)) ∧ ((p2 ∨ p3) ∧ (p2 ∧ False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350983423164029516746400570034 : (p4 → (((p3 ∨ p2) ∨ ((((p3 → (p4 ∧ p2)) → ((p5 → (p5 ∨ False)) ∨ (p5 ∧ p4))) → ((p3 → p5) → p5)) ∧ p1)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115340151987514617099141904300 : (((p4 ∨ (((((p1 → p3) → p2) → p3) → p3) → p2)) → (((p5 ∧ ((True → (p4 ∧ p3)) → p3)) → (p3 ∨ p3)) ∨ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646330477101727502811021098902 : ((((False → (p1 ∧ ((True → (False ∨ (p1 ∧ p2))) → ((((p3 ∨ p1) ∧ p3) → ((False ∧ True) ∧ (False ∨ p4))) ∨ (p2 ∨ p5))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215285855933591949016697194319 : ((p1 ∧ ((p4 ∧ p3) ∧ True)) ∨ (p2 → (((False ∧ ((p1 ∨ (True → ((p1 → (p4 → (p4 ∨ True))) ∨ True))) → False)) ∨ (p2 ∨ p2)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81897101379797777041674830625 : (((((((((p3 ∧ p2) → p4) → p5) ∨ (((False → p3) → p1) ∨ (False → False))) ∧ p1) ∨ p1) → (p4 ∨ True)) → (p3 ∨ (False ∧ p2))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p3 ∧ p2) → p4) → p5) ∨ (((False → p3) → p1) ∨ (False → False))) ∧ p1) ∨ p1) → (p4 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56693679394076553599897814205 : ((((False ∧ p1) ∨ p2) ∧ (p5 → (((True → (((p5 ∨ p1) → (False ∧ p4)) ∨ ((p5 ∧ (p1 ∧ p4)) ∨ (p5 → p3)))) ∨ p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214320837108147857851979054287 : (((False ∨ (True → p4)) → p5) ∨ ((True → (((p1 ∧ p2) ∨ (((True ∧ (p2 ∨ (p3 ∨ p4))) → p4) ∧ p4)) ∧ p5)) ∨ ((False ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112766269125913955573098249956 : (((((((((p1 → p1) → False) ∧ False) ∨ True) ∧ p4) ∨ p3) → ((((p4 → True) → ((True ∨ p4) → False)) ∨ p4) → p4)) → p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264162548674655663897197278511 : (True ∧ (((p5 ∧ (p2 ∨ (True ∧ p5))) ∨ (p3 ∨ p4)) ∨ (True ∨ ((p5 → ((p2 ∨ p3) ∧ ((True → ((False ∧ p4) → p4)) ∧ False))) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715683829115961400440257037148 : ((((((False ∧ True) ∧ False) ∨ p3) ∧ ((((p4 → p5) → (p4 ∨ False)) ∨ (p2 → (p4 ∨ p4))) → (((False ∧ (True → p5)) ∨ p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67470923749787377747376599740 : ((p1 → (((p1 → p2) ∨ (p3 ∨ ((p2 → False) ∨ ((False ∨ ((True ∨ p3) ∧ p5)) → False)))) ∨ (p2 → (p2 → ((p3 ∨ p3) → p2))))) ∨ p1) := by
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
theorem thm_5_vars_356026130233101595059026379971 : (p5 → ((((True → (((False ∧ ((p1 → True) → True)) ∨ True) → (p4 ∨ p4))) ∨ p5) → ((p4 ∧ False) ∧ p3)) ∨ (True ∨ (p4 ∨ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171767688508753530101048531629 : (((((p4 ∧ p1) ∨ (((p5 ∨ (True ∨ False)) → (p4 ∧ True)) ∨ p5)) → p4) → p4) ∨ (False → ((((p3 ∧ (True ∨ p5)) ∧ False) ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348803871860468317084531075685 : (p3 → (p1 ∨ (((p5 ∧ p5) → (((p3 → (((p2 ∧ False) → p1) ∧ ((p4 ∨ p2) ∧ p5))) ∧ (p4 ∨ True)) ∧ False)) ∨ (p2 → (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40569354923658735901181581582 : ((((p5 → ((False ∨ (((((p3 ∧ (False → p5)) ∧ p3) ∨ p3) ∨ (p5 ∧ (p3 ∨ True))) ∨ ((p2 → p4) ∧ False))) ∧ True)) ∨ p2) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206969160155119452148269583922 : ((((p2 ∨ (p5 → p3)) → p2) ∧ p1) → (p2 ∨ ((((p1 ∨ p4) ∨ ((p3 ∨ p1) ∧ p4)) ∧ ((p3 ∨ p5) → False)) ∨ ((p1 ∨ p5) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597695416620958893378737968393 : ((((((p4 ∧ p4) → (False ∨ p4)) → (True ∧ ((p1 ∧ ((p4 → (p5 ∧ ((p4 → (p5 → p3)) ∧ True))) ∨ (p1 → p5))) ∨ p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261431221333607837749219450321 : ((p5 → p2) → (((((p2 → p2) ∧ ((False ∧ ((True → p4) ∧ (True ∨ p5))) ∨ p4)) ∧ True) ∨ (((p3 ∧ p5) ∧ p2) → (p2 → p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350395478060082599322519358637 : (p4 → (((True → ((p4 → (((((p1 ∧ False) ∧ (((True → p1) ∧ True) ∧ False)) ∨ (p5 ∧ (False ∧ p3))) → p1) ∨ p1)) ∧ False)) ∧ p1) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234809742999801000151071754327 : ((p5 → (p5 ∧ p4)) → (((((p1 ∧ (p5 ∧ True)) ∨ (p1 ∧ p2)) ∨ p1) ∨ ((False → p1) ∨ (p3 ∨ (False ∨ (p4 → p1))))) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137706535990608026003829008278 : ((p1 ∨ ((p3 ∧ (p5 ∨ ((((True → True) → p5) ∧ p4) ∧ (False → p5)))) ∨ (True ∨ ((p2 → (p2 → p4)) ∨ False)))) ∨ (True → (p1 → p4))) := by
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
theorem thm_5_vars_184414391913998354423599267297 : (((((p2 ∨ (True → (p1 → p2))) ∨ p4) → p2) ∧ (False ∧ p5)) ∨ (False → (((((p3 → p1) → p2) ∧ (p4 → p5)) ∨ (p1 → p1)) ∧ p5))) := by
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
theorem thm_5_vars_797908788057868130923626733799 : (((p1 → ((p5 ∨ ((p4 ∧ True) → (((p2 → (p5 ∨ (p5 ∨ (((p2 → (p5 ∧ p3)) ∧ p5) ∨ True)))) ∨ True) ∧ p5))) ∨ (True ∨ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263796596041594626959568773438 : (True ∧ (((p1 ∨ (p1 ∧ (True ∨ (((p2 ∧ p1) → False) ∧ (p1 ∨ p5))))) → (p2 ∧ p3)) ∨ (True ∨ (p5 ∨ ((False ∧ True) → (False ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804943696468957721484424938112 : (((p3 → ((p1 → p4) ∨ (p2 ∨ (((p5 → ((p5 → (p3 → (True → (p3 → p4)))) ∧ (((p2 ∨ p1) → False) → p1))) ∨ p2) ∨ p3)))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114178836263533088288019769677 : ((((False ∧ (((p4 → p2) ∨ p1) ∨ ((False → ((p4 → p1) ∨ (False → p4))) ∨ p5))) → (True ∧ p4)) → (p5 ∨ (True → p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136470308656330082542243435059 : ((((p2 ∨ p1) ∧ p3) ∧ (((p4 ∧ p2) ∨ ((p3 ∧ p1) ∨ (False ∨ ((p4 → p5) → (p4 ∨ (p1 ∧ p5)))))) ∨ p2)) ∨ (False → (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313288951643418813177533739419 : (p3 ∨ ((p4 ∧ (((False → p2) → p3) → (p2 ∧ (((((((p1 ∨ True) ∨ p5) ∧ p1) → p5) → (p2 → p1)) ∨ (p3 ∨ p5)) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764191207726779571574386580435 : (((p3 ∧ (p5 → (True ∧ (((((True ∧ (p4 ∧ p2)) ∨ ((p5 → p4) ∧ p5)) ∨ (((p2 ∧ p1) ∧ (p3 → False)) → p2)) ∧ p3) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3353979291132781918799809481 : ((p3 ∨ False) → ((p2 ∨ ((p5 → (p4 ∨ p2)) ∨ ((True ∧ p5) → ((((p3 ∧ (p4 ∨ p1)) → (p4 → p1)) ∧ p4) → False)))) ∨ p3)) := by
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
theorem thm_5_vars_112879297230469712044497734166 : ((((True ∧ p2) ∧ ((p1 ∧ (((True → (p4 ∨ (p3 ∧ p5))) ∨ p3) → (p4 ∨ True))) → (p2 ∨ ((p4 ∧ p3) ∧ p1)))) → False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50337086130983051623599189220 : ((((p4 → (p2 → ((False → (True ∨ True)) ∨ p1))) → (((p5 → True) ∨ p2) → (p5 ∨ (p4 ∨ p3)))) ∨ (p2 → (p4 → (p4 ∧ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651252021558775510015012680523 : ((((((True ∧ p5) → False) ∧ ((p3 ∨ (p4 ∨ ((p5 ∨ p5) ∨ ((p3 ∧ p2) ∧ p3)))) ∨ (False → ((p4 ∧ p2) ∨ p5)))) ∧ (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682616370499869059374135564661 : (((((p2 → (False ∨ (p3 → (False → (p1 ∨ p2))))) ∨ (((p4 ∨ (p5 ∧ p1)) ∨ p5) ∧ p3)) ∧ ((p2 → p4) → (False ∨ (p4 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135293875984278577002820357307 : ((((((p2 → (False ∨ (True ∧ ((p5 → p2) ∧ p1)))) ∧ p4) ∧ (p3 → (False ∧ p5))) ∧ p5) ∧ ((p1 → p4) → p2)) ∨ (False → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656292247645727914652104738876 : (((((p3 → (p2 → (False ∧ ((p4 ∨ (True → (True ∨ p5))) ∨ p2)))) ∧ ((False ∨ p3) ∧ (p1 ∧ ((p3 ∧ p4) ∨ p1)))) ∨ (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135444691181337571261847259617 : ((((((False → p4) ∧ True) ∧ (p5 → (((False ∧ (p2 → (p2 ∧ p3))) ∨ p3) → False))) ∧ p1) → ((True ∧ p4) ∧ p3)) ∨ (p4 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258808666555656302432669596314 : ((True → False) → (p2 ∨ (((p1 ∧ (((((p2 → ((False ∨ p3) ∨ False)) ∧ (p2 → p4)) ∨ (True ∧ True)) → p1) ∧ (True → p4))) → p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64115014077071841877484994342 : ((False ∨ ((p4 ∨ ((p5 ∨ (False → p3)) ∧ p2)) ∧ ((False → p4) → ((((False → p3) ∧ p2) ∨ (((p3 ∧ p1) → False) ∧ p4)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213476228074997841063127540887 : (((p1 → (False ∧ p2)) ∧ p3) ∨ (p1 ∨ ((False ∧ (p3 → (p4 → p2))) ∨ (((p5 ∨ (((p3 ∨ p1) ∨ True) ∨ p3)) ∧ (p2 → p5)) ∨ True)))) := by
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
theorem thm_5_vars_111849836850344088160572993522 : (((((False → (False ∨ ((p3 ∧ p2) ∨ ((False ∨ p5) ∨ p1)))) ∨ ((p1 ∨ (p4 ∨ False)) ∧ p2)) → (p1 → (False ∨ p2))) ∨ True) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618295617622999825229339288404 : ((((((p1 ∨ p1) ∨ (p3 ∨ p2)) ∨ (p2 ∨ ((((p4 ∧ p5) ∧ ((False ∧ p3) → (p1 ∧ p3))) → p2) ∧ (p2 → (p3 ∨ p5))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165749334920432317621199829644 : ((((p2 → False) → (p4 ∧ False)) ∨ ((p3 ∨ (p2 ∨ ((p5 ∧ False) ∧ p1))) ∨ (p2 ∨ p2))) ∨ (p5 ∨ (True ∧ (((p1 ∨ p5) ∨ False) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134796250032202741891670757373 : (((p3 ∧ ((((False ∧ p5) ∧ p4) → p3) ∨ (((p3 ∧ (p1 ∧ (True ∨ True))) → ((p1 ∨ p5) → p5)) → p5))) → p1) ∨ ((p2 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342663306779894989739988845713 : (p2 → (((((p3 ∧ p5) ∨ p2) → False) → ((p1 ∧ p4) ∨ p5)) ∨ (False ∨ ((((False ∧ (p5 ∧ p2)) ∧ (p3 → True)) ∨ (True ∨ p5)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ p5) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57814566318469611686845111522 : (((p3 ∧ (p2 ∧ p1)) → ((((p3 ∨ p2) ∨ (p4 → (p3 ∨ True))) → ((p5 ∧ p5) ∨ (True → ((p2 → p5) ∨ (p2 ∧ p2))))) ∨ p5)) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165558087661577575343023426566 : (((p1 ∨ (p1 ∨ (p3 ∨ ((p1 → p1) → p1)))) ∧ ((p4 → (p5 → (p4 ∨ p5))) ∧ p5)) ∨ ((False ∧ False) ∨ (p4 ∨ (p5 → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_717417852352120096239510746662 : ((((False → ((p4 → p3) ∨ p5)) ∧ ((((p3 → p1) → p5) → False) ∨ ((p2 → False) → (((((p2 ∨ p1) ∧ p1) ∧ p4) → p5) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164570200605190035460940682710 : (((((False ∨ False) → p4) ∧ (False → (False → (p1 ∧ (p2 ∧ (False ∨ (False ∨ p5))))))) ∧ p5) ∨ (p1 → (p4 ∨ (p4 ∨ (p4 → (p1 ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172079892972813741376741956640 : (((((p4 ∨ True) ∨ (p1 ∨ p4)) ∨ (((p1 → True) → p5) ∧ p4)) → (False ∧ True)) ∨ ((p5 → (p5 ∨ (p3 ∧ (p3 → False)))) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57950151246662261894483354402 : (((p1 → (p1 ∨ p3)) → (((True ∨ (p3 ∨ (False → p1))) → p4) → ((p3 ∧ (((p5 ∨ (p5 → p4)) ∧ p5) → (False → p3))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184469071726353635677857195762 : (((((p5 ∨ p5) ∨ ((False → p1) → p4)) ∧ p5) ∨ (False → p4)) ∨ ((((p4 → (p4 ∧ (p1 ∨ (p5 ∧ (p5 → False))))) ∧ p1) → False) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57658721275236897052806195385 : ((((p4 ∨ True) ∨ p1) → ((p2 ∨ ((p5 → ((p5 ∨ p5) ∨ True)) ∧ p5)) ∨ ((((((True ∧ p4) ∨ False) ∧ p3) ∨ p3) ∧ False) → True))) ∨ p2) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165660731902116666221683035646 : ((((p3 ∧ p2) ∨ (False ∧ (p3 ∨ p4))) ∨ (True ∨ ((p5 → (p4 ∨ False)) ∨ (p5 → p5)))) ∨ (False ∨ (((True ∨ p5) → (p1 → p1)) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150359445885123215055522085067 : ((p5 → (True ∧ (((((p1 ∨ (((p5 → False) → p5) ∨ p2)) → p4) ∨ (False → p5)) ∧ p2) → (p4 ∨ p1)))) ∨ ((True ∧ p4) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_197416898525203497193356107569 : (((p3 → ((False ∨ (False ∨ p1)) ∧ p1)) → False) ∨ ((False ∨ (((p1 ∧ (p1 ∨ p3)) → ((p1 ∨ False) ∨ False)) ∨ ((False → False) ∧ p5))) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118337050677570121560571127909 : ((p2 ∨ (((p4 ∧ ((p2 ∨ False) ∧ (p5 ∨ ((p5 ∧ p3) ∧ ((p3 ∧ (((True → p2) ∧ p4) ∧ p2)) → True))))) ∨ p2) ∨ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249547377128584738054772690266 : ((p5 ∨ p2) ∨ ((((p2 → ((p3 → True) ∧ ((((p1 ∧ (False ∨ p2)) ∨ (p5 ∨ p5)) → p2) → p3))) ∧ p3) ∨ True) ∧ (p5 ∨ (p3 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168374422068952389655735999510 : (((p4 ∨ p2) ∨ (((((p5 → False) ∧ False) → ((p2 → p2) → p2)) → True) ∧ (p2 → False))) → (((p5 → p2) ∧ (p3 ∧ (p3 ∧ p1))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198391100307008185640512447802 : ((p3 ∧ (p3 ∧ ((p5 ∨ p4) ∧ (p3 ∨ p3)))) ∨ (((p3 → False) ∨ p1) → (True ∨ (p2 → ((False ∧ False) → ((p2 ∧ False) ∧ (p2 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137034220863931719156681320983 : (((p5 ∨ p2) → ((False ∨ (p3 → (p3 → p2))) → (((p4 ∧ p2) → ((((p2 ∧ True) ∨ False) ∧ False) ∧ True)) → p2))) ∨ ((p5 → p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353550286878895077924407838481 : (p4 → (p3 ∨ (((False ∨ ((p1 ∧ False) ∨ ((p5 ∧ (p4 ∨ p3)) ∧ (((False ∧ p3) ∨ True) ∨ p2)))) ∨ p2) ∨ ((p3 → (True ∨ p4)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111634883527950218669393797438 : (((((((((p2 ∨ (p4 ∧ p3)) ∨ p3) ∨ p5) ∨ p1) ∨ (p3 ∨ True)) ∨ (True → (p1 → ((p3 ∧ p1) → p2)))) ∨ p1) ∨ p5) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



