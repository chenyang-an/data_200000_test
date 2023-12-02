variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4207667444649695963378464110 : (p5 ∨ (((((p4 → p2) ∨ p5) ∧ p2) → (((True → (p4 → (p5 ∧ (((p5 → p1) ∨ p3) ∧ p5)))) ∨ (True ∨ p5)) ∧ p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118654710125445504984728384946 : ((p4 ∨ (p4 ∧ (p1 → (((p3 → (p3 ∨ (p5 ∧ (p1 → (((True → (p2 ∨ p5)) ∧ p4) ∧ True))))) → p4) ∨ (p4 ∧ p1))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157991649737677226478213049834 : (((((p3 → p2) → p4) ∧ ((p5 ∨ False) → p2)) → (p1 ∨ (False ∨ (False ∨ ((True ∨ True) → p2))))) ∨ (((p2 ∨ (p2 ∨ p3)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158500048920123361183030861876 : (((p5 ∧ True) → (p4 ∧ (((p1 ∧ True) → p5) → ((((p5 ∨ p1) ∧ False) → p5) → (True → p1))))) ∨ ((p3 → p3) ∨ ((p1 ∧ p1) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746369608432842371625813669133 : ((((p2 ∨ False) → (p2 → (p1 ∨ ((False ∧ (p5 → (p4 → (((((True ∨ (p2 → (p5 ∨ p3))) ∨ p3) ∧ p4) ∧ False) ∧ False)))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338944477611806314440034308032 : (p1 → ((p5 ∨ False) → ((True → p4) ∨ ((p3 ∨ (((p3 ∧ False) ∧ (p3 ∨ p2)) ∨ ((((p2 → p5) → False) ∧ (False ∨ p1)) → p2))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344434777845683419261261024612 : (p2 → (p5 ∨ ((((True ∨ False) ∨ (True ∨ p2)) ∨ p5) → ((((p3 ∧ True) → True) → ((False ∨ p4) ∨ (p3 ∨ (p4 → (False → True))))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809152716940587852179638202940 : (((p5 → ((((((p2 → p2) → False) ∨ ((p4 ∨ False) ∧ p2)) ∧ (True ∧ ((p1 ∨ (((p2 ∨ p2) ∨ p2) ∨ True)) ∧ True))) ∨ p2) ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_175163708642527797959131760303 : ((True ∨ ((((p1 ∨ ((p4 ∨ (p3 ∨ True)) → p3)) ∧ p1) ∧ (True ∧ p2)) → p3)) → (((p1 ∧ False) ∨ (False ∨ (True → (False → False)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315748671550371332324998006720 : (p3 ∨ ((p4 → p5) ∨ ((p4 ∨ (((p1 → (True ∧ (((p5 ∨ True) ∨ False) → True))) → p1) ∨ ((p1 ∧ p2) ∧ p3))) ∨ (True ∨ (p2 ∨ p1))))) := by
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
theorem thm_5_vars_48201157151298875990982866700 : ((((False ∧ p1) → (((p4 → p3) ∨ p5) → ((False → ((p1 ∨ ((p5 → p5) ∨ (p3 ∨ p3))) ∨ (False ∧ True))) ∧ p3))) → (p3 → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64478920313165261881004524455 : ((p1 ∨ (((True → p3) → (p4 ∨ (((True → p2) ∨ (p3 → ((p1 ∨ p1) ∨ p2))) → (p3 ∨ p5)))) ∧ ((p5 ∨ False) ∨ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140065541837345372113360762380 : (((((p5 ∨ p1) ∧ p2) ∧ ((p1 → (((p5 ∨ ((p2 ∧ False) → p2)) ∧ (p1 → p1)) ∧ True)) → p5)) ∨ (p1 ∧ p3)) → (p3 ∨ (p5 ∨ False))) := by
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
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p1 → (((p5 ∨ ((p2 ∧ False) → p2)) ∧ (p1 → p1)) ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190108785917286574077375368453 : (((((p5 ∧ True) ∧ p1) ∧ (p5 ∧ (p4 ∨ p1))) ∧ p4) ∨ ((((False → p2) ∧ (True ∨ (False ∨ (((False → p4) ∨ True) → p5)))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304044008197532145682890571464 : (p1 ∨ ((p4 ∧ (False ∨ (p5 ∧ ((p4 → (((p1 → (p3 → ((True → p2) ∧ p5))) ∨ (False ∨ (True ∧ p1))) ∨ p2)) → (p1 ∧ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354193844893264186763989972691 : (p5 → ((((((p2 ∨ p3) ∨ (p1 ∧ False)) → p5) → (False ∧ ((True ∧ (True ∨ (p4 → (p1 → p1)))) → ((p1 ∨ p1) ∧ p1)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171821771851931272870664379361 : ((((((True ∧ p1) ∨ False) → False) ∨ (p3 → (p5 ∧ (False ∨ (False ∨ p1))))) → p1) ∨ (((True ∨ p2) ∨ p4) ∨ (((True → p3) ∨ p4) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199739666822334007114349640236 : (((p2 ∨ (p1 → ((p4 → True) ∨ p5))) → p3) → (True ∧ (p3 ∧ ((((p2 ∧ ((False ∨ True) ∧ p5)) ∨ p3) ∨ p1) ∧ (True ∨ (p2 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (p1 → ((p4 → True) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (p1 → ((p4 → True) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656923427243976246463082471967 : (((((p1 ∧ (False ∨ (p4 → True))) ∨ ((p4 ∨ (p3 ∨ p1)) ∧ (((p1 ∧ (p3 → p4)) ∨ (p3 ∨ p1)) ∨ (p4 ∧ p5)))) ∨ (False ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_213432910400180310512427675967 : (((p4 ∨ (p1 ∧ p5)) ∧ p5) ∨ (((p2 ∨ ((p5 → (p1 ∨ True)) → True)) ∨ p3) ∨ ((p4 ∨ (((p5 ∧ p3) ∨ p3) ∨ (p5 → p2))) → p3))) := by
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
theorem thm_5_vars_219426411942751064612959389362 : ((p4 ∨ ((p5 → True) ∧ True)) → ((((p2 ∧ (p2 → p4)) ∨ ((((p2 ∨ False) → (p3 ∨ (p1 ∧ p4))) → (p1 ∨ p4)) ∨ p4)) → p2) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114040327457131072666530357811 : (((((p3 ∨ (p5 ∨ p3)) ∨ ((((p4 → p2) ∨ False) ∧ (p2 ∧ p3)) → (p3 → p5))) ∧ (p1 → p3)) ∨ (p5 ∧ (True → p1))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485484439640562926199368003593 : ((((((True → (p4 ∧ p2)) → p5) ∨ p3) ∨ (((True ∧ ((p3 ∧ False) ∨ True)) ∧ True) ∨ ((((p4 ∨ (p2 ∨ p5)) ∧ p5) ∨ p1) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59929356859816468239158771716 : (((True ∨ True) → ((False ∨ (((p2 ∨ ((((p3 ∨ p2) → ((p2 ∧ ((p3 → False) → p3)) → p5)) → p2) → p4)) ∧ True) ∨ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158126973224732328861941182265 : (((((p4 ∧ True) ∨ p1) ∧ p1) ∨ (p2 → (((p5 ∨ p3) ∨ p4) ∨ (p2 ∨ (p3 → (p1 → p1)))))) ∨ ((p1 ∨ (False ∧ (p1 ∨ False))) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_351570131050597087897761988358 : (p4 → (((True ∨ (p3 → ((p5 → p1) → (p3 ∧ p2)))) ∧ ((False → True) → ((True ∨ p2) → p5))) → ((p5 ∧ ((True ∧ p5) ∨ False)) ∨ p2))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h12
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115394834853964877412154917238 : (((False ∧ (p1 ∧ (((p2 ∨ p5) ∧ p1) ∨ p1))) ∧ (p4 ∨ ((False → p5) → ((p4 → (p2 → p5)) ∧ ((True ∧ p5) → p2))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632864359645926515381086236697 : (((((((False ∧ (p3 ∨ p3)) ∨ ((False ∨ (((p5 → p3) ∨ (True ∨ p4)) ∧ True)) → ((False ∧ False) → True))) → p4) ∧ (p5 ∧ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246326144374060126110500259717 : ((p4 ∧ p5) ∨ (((((((p4 ∧ p5) → ((p1 ∧ p4) ∨ p3)) ∧ (p5 ∨ p2)) ∨ p2) ∧ p2) → ((True → False) → (p5 ∧ p1))) ∨ (p3 ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h28 := h2 h27
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103009013988683340714567351861 : (((((p3 ∧ True) ∧ (((p4 ∨ p4) ∨ (p3 ∧ False)) ∧ p3)) ∨ (p2 ∨ ((((False ∨ p3) ∧ False) → (False ∧ p5)) ∨ p2))) ∨ p4) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339482253942110072707594361714 : (p1 → (False ∨ ((((p2 ∧ p5) → ((p3 ∨ ((True ∧ p4) ∨ (True → p4))) ∧ p1)) ∨ (p2 → (p1 → (((p5 ∨ p2) ∨ False) ∨ p2)))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346302415933700648873627520925 : (p3 → (((((((False ∨ (p1 ∧ p2)) → (p1 → p2)) ∧ (p1 → p5)) ∨ (True ∨ (p1 ∨ ((True ∧ p1) → p3)))) ∧ p3) → p2) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611602495477609965231180867344 : (((((p1 ∨ ((p2 ∨ ((p4 → ((True → ((p3 ∨ p3) ∧ p1)) → p5)) → (p1 ∧ (p2 ∧ p2)))) ∧ ((p2 ∧ p4) → p5))) → p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951941998751712667108767825412 : ((((p5 → (False ∧ p2)) ∧ ((p4 ∨ ((True ∧ p2) → (p3 → p5))) ∧ ((False → (p4 ∧ (((p3 → p5) → (False → False)) → p2))) → p5))) → p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (False → (p4 ∧ (((p3 → p5) → (False → False)) → p2))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h8
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191557121874679340350799021218 : ((p1 ∧ (False ∨ (((p3 → p5) ∧ (True ∨ p3)) → p4))) ∨ (((p2 → p3) ∧ p5) → (p5 ∨ ((p3 ∧ p2) → ((p4 ∨ (False ∨ p4)) ∨ p4))))) := by
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
theorem thm_5_vars_156794270540036940869848810873 : (((p3 ∧ ((True ∨ True) → ((((p4 → (p5 → p2)) → p1) ∨ (p2 → (p5 ∧ False))) → p4))) ∧ False) ∨ (False → (p3 ∧ (p2 → (p4 ∨ p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763209508652641250761607534768 : (((p3 ∧ ((p2 → p4) ∧ (((p5 → (p2 ∧ p5)) ∨ p5) ∨ (p4 ∨ ((p4 → ((p4 ∧ False) ∧ (((p5 ∧ p3) ∨ False) ∧ p3))) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316499305074129529990249775442 : (p3 ∨ (p2 ∨ (((((p3 → p5) → p1) ∨ (((p3 ∨ (p3 ∧ (p1 → True))) → p2) → p1)) → (((p3 ∨ p4) ∧ p4) → False)) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217802128579595572001323098601 : (((p1 ∨ (p4 ∨ True)) → p3) → (((p4 → p2) ∧ p5) → (True → ((p1 ∨ ((((p3 ∨ (p4 → p2)) ∧ True) ∧ p1) ∨ (p2 ∨ p3))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179322877222756546690285466958 : ((p1 ∨ (((p5 → (p4 ∧ p4)) ∧ (p4 ∨ (False ∨ (p2 ∨ p2)))) ∧ p5)) ∨ (p5 → ((p3 → p2) → (((p3 ∨ (p1 ∧ p3)) → True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710790403447021723468068643609 : (((((p2 → (p4 ∨ p4)) → (False ∨ p5)) ∧ ((False ∧ (((p4 ∨ p2) ∨ (False → (p3 ∨ (((p2 → p4) ∧ p1) ∧ p2)))) ∧ False)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199764069250348387993386614543 : (((p1 → ((p4 → (p1 ∨ True)) → False)) → p2) → (((((((p4 ∧ False) ∧ p5) ∨ (p4 → p3)) ∨ (p3 ∨ True)) → p3) ∧ p2) → (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p4 ∧ False) ∧ p5) ∨ (p4 → p3)) ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748239918340276323881306114343 : ((((p2 → True) → (((True → (p2 ∧ (((p3 ∧ (False → p4)) → p5) ∨ p4))) ∨ p4) ∨ (p4 ∨ ((p3 ∧ ((p2 ∨ p2) ∨ p5)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228420816178971589160614727038 : ((False ∨ (p3 ∧ p2)) ∨ (p3 → ((p4 ∧ False) ∨ ((p3 ∧ ((False ∧ p4) ∧ ((p1 ∨ (p5 → p3)) ∨ (p3 → (p4 → p1))))) → (p5 → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323164999776951233766132753247 : (p5 ∨ (((((p5 ∧ ((p5 ∧ ((p1 ∧ True) ∨ p5)) → (p4 → (p1 ∧ (p2 ∨ (p3 → p3)))))) ∨ (True ∨ False)) ∧ p3) ∧ True) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357070584369924232182774287587 : (p5 → (((p5 → p1) ∧ p1) → ((p4 ∧ ((p2 ∨ p4) → (p4 ∧ (p2 ∧ (p3 ∧ (p1 ∧ (p4 ∨ (p2 ∧ (p5 ∨ True))))))))) ∨ (p3 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191315395417796453815106314582 : (((True ∧ False) ∨ ((p5 → (p2 ∨ (p4 ∨ False))) ∧ p2)) ∨ (p4 ∨ (p2 ∨ (True ∨ (p5 ∨ (((p4 ∧ p1) → ((p2 → False) ∨ p5)) ∧ p5)))))) := by
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
theorem thm_5_vars_316703483824723480427413232944 : (p3 ∨ (p5 ∨ ((p4 ∧ p2) ∨ ((p1 → p5) ∨ (((False → (((((p2 ∨ (p1 ∨ True)) ∧ p4) ∧ False) ∧ False) ∨ p1)) → True) → (p3 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51022019171848634928376729924 : (((p2 ∧ ((p3 ∨ p1) → (p3 ∨ (p5 ∨ (((p1 ∧ p4) → ((p3 ∧ p3) ∨ True)) ∧ False))))) ∧ ((p5 → ((p3 ∧ p5) → p4)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50295682484843630162205790077 : ((((((((p4 → ((p2 ∧ (p3 ∨ False)) → p2)) ∨ p5) ∨ p4) → True) → p3) ∨ (False ∨ (p5 ∨ p4))) ∨ (True ∨ (p3 → (p2 ∧ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232844194353437284926406793073 : ((p2 ∧ (True → False)) → (((((((p1 ∨ False) ∨ False) ∧ p3) ∨ p5) ∨ True) ∨ (True ∨ (True ∨ p3))) → (p2 → (p1 → (p3 ∧ (p3 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h1.left
            let h13 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h14 =>
            -- False on the left can always be used.
            apply False.elim h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h1.left
      let h29 := h1.right
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h30 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h31 := h29 h30
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h1.left
        let h35 := h1.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h37 := h35 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h1.left
        let h40 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h38
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- Conjunctions on the left can always be decomposed.
            let h48 := h1.left
            let h49 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h45
          case inr h50 =>
            -- False on the left can always be used.
            apply False.elim h50
        case inr h51 =>
          -- False on the left can always be used.
          apply False.elim h51
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h1.left
        let h54 := h1.right
        -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
        have h55 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h54, we can now drive its conclusion.
        let h56 := h54 h55
        -- False on the left can always be used.
        apply False.elim h56
    case inr h57 =>
      -- Conjunctions on the left can always be decomposed.
      let h58 := h1.left
      let h59 := h1.right
      -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
      have h60 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h59, we can now drive its conclusion.
      let h61 := h59 h60
      -- False on the left can always be used.
      apply False.elim h61
  case inr h62 =>
    -- Disjunctions on the left can always be decomposed.
    cases h62
    case inl h63 =>
      -- Conjunctions on the left can always be decomposed.
      let h64 := h1.left
      let h65 := h1.right
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h66 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h67 := h65 h66
      -- False on the left can always be used.
      apply False.elim h67
    case inr h68 =>
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h69 =>
        -- Conjunctions on the left can always be decomposed.
        let h70 := h1.left
        let h71 := h1.right
        -- We want to use the implication h71 based on <expert-advice>. So we show its premise.
        have h72 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h71, we can now drive its conclusion.
        let h73 := h71 h72
        -- False on the left can always be used.
        apply False.elim h73
      case inr h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h1.left
        let h76 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h74
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h77 =>
    -- Disjunctions on the left can always be decomposed.
    cases h77
    case inl h78 =>
      -- Disjunctions on the left can always be decomposed.
      cases h78
      case inl h79 =>
        -- Conjunctions on the left can always be decomposed.
        let h80 := h79.left
        let h81 := h79.right
        -- Disjunctions on the left can always be decomposed.
        cases h80
        case inl h82 =>
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h83 =>
            -- Conjunctions on the left can always be decomposed.
            let h84 := h1.left
            let h85 := h1.right
            -- We want to use the implication h85 based on <expert-advice>. So we show its premise.
            have h86 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h85, we can now drive its conclusion.
            let h87 := h85 h86
            -- False on the left can always be used.
            apply False.elim h87
          case inr h88 =>
            -- False on the left can always be used.
            apply False.elim h88
        case inr h89 =>
          -- False on the left can always be used.
          apply False.elim h89
      case inr h90 =>
        -- Conjunctions on the left can always be decomposed.
        let h91 := h1.left
        let h92 := h1.right
        -- We want to use the implication h92 based on <expert-advice>. So we show its premise.
        have h93 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h92, we can now drive its conclusion.
        let h94 := h92 h93
        -- False on the left can always be used.
        apply False.elim h94
    case inr h95 =>
      -- Conjunctions on the left can always be decomposed.
      let h96 := h1.left
      let h97 := h1.right
      -- We want to use the implication h97 based on <expert-advice>. So we show its premise.
      have h98 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h97, we can now drive its conclusion.
      let h99 := h97 h98
      -- False on the left can always be used.
      apply False.elim h99
  case inr h100 =>
    -- Disjunctions on the left can always be decomposed.
    cases h100
    case inl h101 =>
      -- Conjunctions on the left can always be decomposed.
      let h102 := h1.left
      let h103 := h1.right
      -- We want to use the implication h103 based on <expert-advice>. So we show its premise.
      have h104 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h103, we can now drive its conclusion.
      let h105 := h103 h104
      -- False on the left can always be used.
      apply False.elim h105
    case inr h106 =>
      -- Disjunctions on the left can always be decomposed.
      cases h106
      case inl h107 =>
        -- Conjunctions on the left can always be decomposed.
        let h108 := h1.left
        let h109 := h1.right
        -- We want to use the implication h109 based on <expert-advice>. So we show its premise.
        have h110 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h109, we can now drive its conclusion.
        let h111 := h109 h110
        -- False on the left can always be used.
        apply False.elim h111
      case inr h112 =>
        -- Conjunctions on the left can always be decomposed.
        let h113 := h1.left
        let h114 := h1.right
        -- We want to use the implication h114 based on <expert-advice>. So we show its premise.
        have h115 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h114, we can now drive its conclusion.
        let h116 := h114 h115
        -- False on the left can always be used.
        apply False.elim h116



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136379391446325088388252605458 : ((((p2 ∨ p2) ∧ (True ∧ p4)) ∨ (((((True ∧ False) → ((p3 → p2) ∨ ((p3 ∨ p3) → p5))) ∨ p5) ∨ p3) → p1)) ∨ ((p3 ∧ p1) → p1)) := by
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
theorem thm_5_vars_178167357862010251586587921247 : ((((False → True) ∨ (p1 → (((p3 ∨ p4) → p3) ∧ (True ∨ False)))) → p3) ∨ (True ∧ ((True ∨ ((p1 ∨ p4) → (p1 ∧ p3))) ∨ (p3 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41637432256483426085394206192 : ((((False → (((True ∧ True) → p2) → (p3 ∧ p2))) → ((True ∧ ((p4 → (True ∧ p5)) ∧ False)) ∧ (p2 ∨ ((p5 → p2) → p5)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820839538012440317509092855208 : ((((((p1 ∨ ((False → (p1 ∨ p4)) ∨ ((True ∨ p2) ∨ ((p4 → p5) → False)))) → False) ∧ (((p5 ∧ (False ∨ True)) → p3) ∧ p1)) ∧ p2) → False) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ ((False → (p1 ∨ p4)) ∨ ((True ∨ p2) ∨ ((p4 → p5) → False)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184128002950472361698650541529 : (((p1 ∧ (((p5 → p5) ∧ (p5 ∨ (False ∨ True))) ∨ p3)) ∨ p1) ∨ (p5 ∨ (((p3 → (((True ∧ True) ∧ (p4 ∨ p5)) ∨ True)) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300047026113677252500559302192 : (False ∨ ((p4 → ((((p3 ∨ ((p1 ∧ p3) ∨ (False ∨ p2))) ∨ True) ∧ False) ∨ (((p1 → p3) ∨ (False → p3)) ∨ (p3 ∧ p1)))) ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171680952137226333585431624225 : (((p2 ∨ (((p4 ∨ p3) → False) ∧ (((p4 ∨ False) → p3) ∧ (False → p3)))) ∨ p4) ∨ (True ∨ ((False ∧ p2) ∨ (p2 ∨ ((p3 → p5) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165237705235974087164352155377 : (((False ∧ (p5 → (p1 ∨ ((True → p1) → (p3 ∨ ((False ∨ p5) ∧ p2)))))) ∨ (p1 ∧ True)) ∨ ((p2 ∧ ((p3 → p4) → (p3 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703667128379564547823780447390 : (((((((p4 ∧ False) ∨ ((p3 → p5) ∨ p1)) ∨ p3) ∧ p3) → (False ∧ ((((p3 → (True → p3)) → (p5 ∨ p5)) → p3) ∧ (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175167713980509627201757840855 : ((True ∨ (((p1 → ((False → ((p1 ∧ p4) ∨ p5)) ∨ p3)) ∧ False) → (p2 ∧ p4))) → ((False ∨ p3) ∨ ((p2 ∨ False) → ((p4 ∨ True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116401724074527003741952391449 : (((p4 ∧ (p2 → p2)) → (((((p5 ∧ ((((p3 → p3) → True) → (p3 ∧ True)) ∨ (p4 ∧ p5))) ∨ True) ∧ p4) → p2) ∨ True)) ∨ (p5 ∧ p2)) := by
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
theorem thm_5_vars_743040204505462979432644746041 : ((((p4 → False) ∨ ((p1 → ((p1 ∧ (p4 ∨ p1)) ∧ ((p5 ∨ ((p2 ∨ True) ∧ (True ∧ (p5 → p5)))) ∨ p3))) ∧ ((p5 ∧ True) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165919537823180201753585275306 : (((False ∧ p5) ∧ (p5 → ((((True ∧ p1) ∧ p3) ∨ (p2 ∨ (False → True))) → (p1 ∨ p2)))) ∨ (p2 ∨ ((p2 ∧ (p2 → (False ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617189955469410531401556898290 : ((((((p5 ∧ ((p2 ∨ False) ∨ True)) ∨ (p1 ∧ p4)) ∨ ((((((p3 ∨ (p2 ∧ False)) ∧ p3) → p2) ∨ (p3 ∨ False)) ∨ p5) → p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_774646136779263086917105719122 : (((False ∨ ((((p3 ∨ p2) ∧ (False → (p1 ∨ p2))) ∨ (p1 ∧ p3)) ∨ (False → (((p2 → ((p4 ∧ (p1 ∧ p4)) ∨ p1)) ∧ p1) ∨ p2)))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_775486609342130339433757921139 : (((False ∨ (p4 ∧ (((p1 ∨ ((((False ∨ (p4 ∧ (p2 ∧ p5))) ∧ ((p3 ∨ p2) ∨ False)) ∧ p5) ∨ (False ∧ p2))) ∨ True) ∧ (True ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346145283293994431138093621506 : (p3 → ((p3 → (((p2 ∧ True) ∨ (((((p2 ∧ (p1 ∨ True)) → ((p2 → True) → p1)) ∧ (p4 ∧ (p3 ∨ p3))) → p1) ∧ p5)) ∧ False)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223869312956145120187316625433 : ((p3 ∨ (True → True)) ∧ (p4 → (((p1 ∧ p1) → p1) ∧ (((((p2 ∨ p3) ∧ True) → p2) ∨ ((False → (p2 ∧ (True ∨ p1))) → False)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37441826447819582232020418254 : (((((p4 → ((False ∨ True) → ((p3 ∧ (((p5 ∨ p5) ∧ p3) ∨ True)) ∧ (True ∧ True)))) → ((True → p4) → (p5 → False))) ∨ p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51607866876165265425833754849 : (((((((p3 → p5) → (((p3 ∨ p4) ∧ (p2 → p1)) ∨ p5)) ∧ False) ∧ p1) ∧ p2) ∧ (p5 ∧ (((p1 ∨ p3) ∨ p2) → (p5 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178746872067583692132439958610 : (((p3 → ((True → p3) ∧ p2)) → ((False ∧ p1) ∧ (p5 → (False → True)))) ∨ ((p2 ∨ ((True ∨ ((p5 → (False → False)) ∨ False)) ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_51934759641768238863428767488 : (((((p3 ∧ ((False ∨ p5) → (p1 → p3))) ∨ p4) ∧ (p1 ∨ (p3 ∨ (p2 → p5)))) ∨ (p2 → ((False ∧ p3) → ((True → p5) ∨ p1)))) ∨ p3) := by
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
theorem thm_5_vars_134512978603299255765897674402 : ((((p3 ∧ (((p5 ∨ p1) → (p4 ∨ ((False ∨ (p5 → (p2 ∧ (p5 → True)))) → (p3 ∧ p1)))) ∨ p3)) ∨ p5) → p1) ∨ ((False ∨ False) → False)) := by
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
theorem thm_5_vars_142286804440074862523264442731 : ((p2 ∧ (True ∧ (((p2 ∨ p4) ∧ p4) ∧ (((p5 ∨ False) ∨ ((p4 ∧ (True ∧ p3)) → False)) → ((p1 → p2) → p5))))) → ((p3 → False) ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178084737239758380605909223518 : ((((((p2 ∨ p3) ∨ ((p2 ∧ False) ∧ p2)) → (False ∨ p4)) → True) → p4) ∨ (True ∨ (((((p1 ∧ p2) ∧ True) ∨ p5) ∨ (p2 ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42868386781706698640672851985 : (((p2 → (True ∧ (((False ∨ ((p4 ∧ ((p2 ∧ p3) → p1)) ∨ ((p2 ∧ p4) ∨ (p3 → ((p3 ∧ p4) ∨ p5))))) → p3) ∨ p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152353079722577074353859828681 : (((((True → p2) ∨ p2) → p5) ∨ (((p3 → (False → ((p4 ∧ p5) ∧ True))) → p2) ∧ (p2 ∨ (p2 ∨ False)))) → (((False → p4) → p3) ∨ True)) := by
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
        -- False on the left can always be used.
        apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713460150688482340089019399095 : ((((p3 → (((p4 → p5) ∧ p4) → False)) ∨ (p3 → (((p5 ∧ p1) ∧ (p2 ∨ p5)) ∨ (((False → ((p5 ∧ p5) → p2)) → False) → p2)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((p5 ∧ p5) → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658208908043631412232844511621 : ((((p5 ∧ ((((((False ∨ p3) → (True ∨ (p4 ∨ p1))) → True) ∧ p4) → (False ∧ (p1 → ((p3 ∧ p4) ∨ p3)))) → False)) ∨ (p1 → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341103270117850485078991413168 : (p2 → ((p4 → (((True → p5) ∧ ((p3 → p4) ∧ (p1 ∨ (p5 → (p4 ∧ ((p2 → False) → (((False ∧ p5) ∨ p4) ∨ p3))))))) ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55263352729432251359760713481 : ((((True ∧ p5) → ((True → p1) ∧ False)) ∨ ((True ∧ (p1 ∨ (((p1 → (p3 ∧ (p1 ∨ (p5 ∨ p2)))) → p5) ∨ (p2 → True)))) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855807707962635784951911767500 : (((((((((p4 ∧ p5) ∨ p4) ∨ (p5 ∨ (((False → (p5 ∨ p2)) ∧ (p2 → p2)) ∧ ((False ∧ False) → p5)))) → p3) → p3) ∨ False) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p4 ∧ p5) ∨ p4) ∨ (p5 ∨ (((False → (p5 ∨ p2)) ∧ (p2 → p2)) ∧ ((False ∧ False) → p5)))) → p3) → p3) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 ∧ p5) ∨ p4) ∨ (p5 ∨ (((False → (p5 ∨ p2)) ∧ (p2 → p2)) ∧ ((False ∧ False) → p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41706532084157772472215341705 : ((((True ∧ (p5 → ((p4 ∨ p4) ∨ p3))) → ((p4 → ((p2 ∨ (p1 ∨ p5)) ∧ ((True ∧ False) ∧ p1))) ∨ ((p5 ∨ p5) → True))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671655016054849216460977449102 : ((((((((((p5 ∧ (p2 ∨ True)) ∨ p3) ∧ (p3 → p1)) ∨ (p1 ∨ p5)) ∧ (p5 ∨ (p5 ∧ p3))) ∨ p2) ∧ p3) → ((p3 ∧ p2) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h39 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708903358039704725540648308422 : (((((((p1 ∨ True) ∨ p4) → False) ∨ (False ∧ p3)) → ((p2 ∧ ((p3 ∧ p2) ∨ (((True ∨ p2) ∧ p2) ∨ (True ∨ p3)))) → (True ∧ p1))) ∨ p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p1 ∨ True) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h20 : ((p1 ∨ True) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h21 := h19 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h27 : ((p1 ∨ True) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h28 := h26 h27
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- False on the left can always be used.
          apply False.elim h30
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h34 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h35 : ((p1 ∨ True) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h36 := h34 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- False on the left can always be used.
          apply False.elim h38
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h41 =>
          -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
          have h42 : ((p1 ∨ True) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h41, we can now drive its conclusion.
          let h43 := h41 h42
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- False on the left can always be used.
          apply False.elim h45
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781425613280499777818803095444 : (((p2 ∨ (p3 ∧ (p3 → ((((p2 ∨ (p5 ∧ p1)) ∨ (p2 ∧ p2)) ∨ p2) → ((p5 ∨ (False ∧ ((False ∧ p1) → (False ∨ p2)))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186826072281032931091664239333 : (((((p5 ∧ p1) ∨ p5) ∨ p3) ∨ ((True → (p1 → True)) ∨ p2)) → ((((((p4 ∧ p1) → p2) ∨ (p5 ∧ (True ∨ p5))) ∨ p4) ∧ p5) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604392963958654419073240175880 : ((((True → (p1 ∧ (((((False ∨ p2) → p4) → (p1 ∧ (((True ∨ (p2 ∨ ((p1 → p3) → True))) ∧ p1) ∨ True))) ∨ p4) → p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111068400564481812171581600461 : ((((((p4 ∨ (p2 ∧ False)) ∧ True) ∨ (p2 ∧ (((True → p2) → p4) ∧ False))) ∨ ((p5 → p2) → (True ∨ (True → p3)))) ∧ False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606312653812719325719745864688 : (((((((((p4 → (((((p1 ∨ True) → (p4 ∧ (p3 → False))) ∨ False) ∧ True) → (p4 ∨ p4))) → p4) ∧ p4) ∨ True) ∨ True) ∧ True) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_650168932976775050588390465832 : (((((p2 ∨ ((((p5 ∧ (p1 ∨ (p1 ∧ True))) ∨ p5) → ((p2 ∨ False) ∨ p4)) ∨ p5)) ∧ (((True → p2) ∨ p2) ∨ True)) ∧ (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47502098847844422360977060509 : (((p1 ∨ (True ∧ (((((True ∨ (p3 ∨ p1)) ∨ (p4 → (True ∧ p5))) ∧ p3) ∨ p2) → (p3 ∨ ((p5 → False) ∨ p3))))) ∨ (True ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699460133142178724354476659732 : (((((((((True ∧ True) → p4) ∧ p4) ∧ p1) ∧ (p2 → p4)) ∨ p2) → (((((p1 ∧ p5) ∨ p2) ∧ ((p2 ∨ p1) → p3)) ∧ False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162008170260709940874404009046 : ((p3 → (False → ((p1 → (p1 → (((p2 → p1) ∨ ((p4 → p4) ∧ p5)) → p3))) ∨ (p5 ∨ p1)))) → (((False ∨ (p3 ∨ p5)) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180498238351284443462167728793 : ((((True ∨ p3) ∧ (p3 ∨ ((True → p5) ∨ p3))) ∧ ((p2 → p5) → p5)) → (((True ∨ (p4 → p4)) → (p2 ∧ (True ∨ False))) → (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ (p4 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : (True ∨ (p4 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h24 := h2 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h29 := h2 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h32 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h33 := h2 h32
        -- We need to get the left conjuct of h33 based on <expert-advice>.
        let h34 := h33.left
        -- One of the premise coincides with the conclusion.
        exact h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h35.left
  let h38 := h35.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h41 : (True ∨ (p4 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h42 := h2 h41
      -- We need to get the left conjuct of h42 based on <expert-advice>.
      let h43 := h42.left
      -- One of the premise coincides with the conclusion.
      exact h43
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h46 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h47 := h2 h46
        -- We need to get the left conjuct of h47 based on <expert-advice>.
        let h48 := h47.left
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h49 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h50 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h51 := h2 h50
        -- We need to get the left conjuct of h51 based on <expert-advice>.
        let h52 := h51.left
        -- One of the premise coincides with the conclusion.
        exact h52
  case inr h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h54 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h55 : (True ∨ (p4 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h56 := h2 h55
      -- We need to get the left conjuct of h56 based on <expert-advice>.
      let h57 := h56.left
      -- One of the premise coincides with the conclusion.
      exact h57
    case inr h58 =>
      -- Disjunctions on the left can always be decomposed.
      cases h58
      case inl h59 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h60 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h61 := h2 h60
        -- We need to get the left conjuct of h61 based on <expert-advice>.
        let h62 := h61.left
        -- One of the premise coincides with the conclusion.
        exact h62
      case inr h63 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h64 : (True ∨ (p4 → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h65 := h2 h64
        -- We need to get the left conjuct of h65 based on <expert-advice>.
        let h66 := h65.left
        -- One of the premise coincides with the conclusion.
        exact h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41174729126901126125106903012 : (((((p4 ∨ ((True ∧ ((p5 → (((p5 → ((p4 ∨ p3) ∧ p4)) → p2) → True)) ∨ True)) ∧ p4)) ∨ p1) → (p3 ∧ (p5 ∨ p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61124422817073945435664169017 : ((False ∧ ((((((p4 ∨ p2) ∨ p3) → p4) → (p1 ∧ False)) → p4) → ((p1 ∨ ((((False ∧ p2) → (p4 ∧ p4)) ∨ p1) → p5)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197044645586968575729388069496 : ((((p4 ∨ False) ∧ (p2 ∨ (True → p5))) ∨ False) ∨ (p4 ∨ (False ∨ (p5 → (p4 ∨ ((((p4 ∨ p2) → (False → True)) ∧ (p2 ∧ False)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_354944049579720143704448239464 : (p5 → ((True → (((p3 → (p5 → (((((p2 ∧ (p2 ∧ (p5 → p5))) ∧ False) ∨ ((p3 ∧ p1) ∨ p4)) ∨ p3) ∨ True))) ∨ p5) ∨ p3)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



