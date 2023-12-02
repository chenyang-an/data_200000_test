variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308472088930106035126240568954 : (p2 ∨ ((((p1 ∨ ((True ∨ True) ∨ (False ∧ (p3 → (p4 ∧ ((True ∨ p1) ∧ p1)))))) ∨ ((p4 ∨ p4) ∨ (p2 ∧ True))) → (p2 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66018415396945575728733764048 : ((p5 ∨ (((p3 → (((p1 → p4) ∧ False) ∧ (((False ∧ p3) ∨ (((p3 ∧ (p4 ∧ p3)) ∧ p1) ∨ p5)) ∧ p4))) ∧ (p2 → p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83972723429939392514153551083 : ((((((p1 → p1) ∨ ((True ∨ ((p4 → p5) → (p4 → p1))) → p2)) ∨ p4) ∧ p2) ∧ ((p5 ∨ (p3 ∧ ((p5 ∧ True) ∧ True))) → p1)) → p2) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195544425712907461237586853202 : (((False ∧ (p2 ∧ p5)) → (False ∧ (p1 → True))) ∧ (((((p5 ∨ (((True → p4) → (False ∧ p3)) ∧ p2)) ∨ True) ∧ False) ∨ (p1 ∨ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54444906908824753717386627042 : ((((((p2 → (True → p1)) ∧ p4) ∨ p2) → False) ∨ (((p2 ∨ ((((p5 → p4) ∧ (True ∨ (p5 → False))) ∧ p5) → p3)) → False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613277620197799850038035650458 : ((((((((p2 → (p5 → p1)) ∧ p5) → p5) → ((p3 ∨ ((True ∨ True) ∧ p2)) → ((p3 ∧ (False ∧ False)) ∧ p4))) → (p2 ∧ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264796821505176433526249821074 : (True ∧ ((p1 ∧ p1) ∨ (p4 → (((p4 → ((p3 → ((p1 ∧ p5) ∨ True)) → p1)) → p5) ∨ ((False ∧ p5) ∨ (p2 → ((p5 ∨ p4) ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40755979355408468584715583805 : (((((p4 → False) ∧ ((p1 ∨ p2) ∧ (p4 → (((((((False ∧ True) → False) ∨ p4) ∧ p5) → True) → (p5 ∨ p4)) ∨ p3)))) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723988969218119688354068191009 : ((((False ∧ (p4 ∨ p5)) ∧ (p4 ∧ ((((p3 ∨ ((((p2 ∧ p5) → p2) ∧ p3) → p1)) ∧ (True → p3)) ∧ False) ∨ ((p3 → p1) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260293889036979193663540231152 : ((p2 → p4) → (((((p2 ∨ (((True ∧ ((p5 → (False → p4)) ∧ False)) ∧ p5) ∨ p1)) ∧ True) ∨ p2) ∨ ((False → False) → True)) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219315096507355394326374376131 : ((p2 ∨ ((p2 → p5) → p1)) → ((((p5 ∧ ((True ∨ p3) ∨ (p2 ∧ (True ∧ (p5 ∨ False))))) ∨ (((p2 ∧ p3) ∧ False) ∨ p5)) ∨ p5) → p5)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h9 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h10 =>
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h13 =>
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
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h20 =>
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h21 =>
            -- One of the premise coincides with the conclusion.
            exact h19
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h29
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h33 =>
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h34 =>
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27574253369962697713667168698 : (((True ∨ False) → ((p4 → (((False → (p5 ∨ ((True → (p5 ∧ ((p5 ∧ p2) → (False ∧ p4)))) ∧ p1))) → False) ∨ (p4 ∨ False))) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695844760480445367912881395544 : (((((p2 ∨ False) ∧ (p3 ∧ ((p4 ∨ (True ∧ p3)) → ((p4 ∧ p1) ∨ p2)))) → (((True → (False ∧ (True ∧ p4))) ∨ (True → p2)) ∨ p1)) ∨ p5) ∧ True) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66250680412532302405060475336 : ((p5 ∨ (((p5 → p4) ∨ (True ∧ True)) ∧ (((p5 ∨ True) ∧ (False ∨ (p5 ∨ (False ∧ p4)))) ∧ (((p1 → False) → p5) ∨ (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139574309664207355529385223735 : (((((p4 → ((False → p5) → (p1 ∧ p2))) ∧ ((p4 ∨ (False ∨ (p1 ∧ p5))) ∨ False)) ∨ (p2 → (p5 ∨ p4))) → False) → (p5 → (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → ((False → p5) → (p1 ∧ p2))) ∧ ((p4 ∨ (False ∨ (p1 ∧ p5))) ∨ False)) ∨ (p2 → (p5 ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163025696976196055551162180298 : (((((True ∧ p3) → (p2 ∧ (p5 → p3))) ∨ ((p2 ∧ p4) ∧ p5)) ∨ ((p1 ∧ p3) → p3)) ∧ ((p4 ∨ (p5 ∨ p1)) ∨ ((True ∨ True) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249657509994963929058129388284 : ((p5 ∨ p4) ∨ ((p1 ∨ ((False ∧ (True ∨ ((p2 → (False ∨ (((False → (False ∧ False)) ∧ (p3 → False)) ∨ False))) → (p2 ∨ p3)))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704915798817877560542503894705 : ((((p4 ∨ ((((p2 ∨ p2) ∨ p3) ∨ (False ∧ p3)) → p1)) → ((((((p2 ∧ p4) → p2) ∨ (p3 ∧ (p4 ∧ p4))) → True) ∨ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216607330636028007612249694374 : ((((p3 → p2) ∧ p2) ∧ p3) → (p1 ∨ (((True → (False ∨ (False → p1))) ∨ ((False ∧ p4) ∧ False)) ∧ ((p2 → (p5 → (p4 → False))) ∨ True)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116051596848716205892122732484 : (((p3 → ((False ∨ p3) ∨ p2)) → (True ∧ (True ∧ (p1 ∧ ((p4 ∨ p4) ∧ (((True ∨ True) ∧ False) ∨ ((p3 → p2) → p3))))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42145109163706054275955459058 : ((((p5 ∨ p5) → (p5 → (((p1 ∨ ((p4 ∨ ((p4 ∧ p2) ∨ p1)) ∧ ((p5 ∧ p2) ∧ False))) ∨ ((False ∧ p3) ∨ p5)) ∧ True))) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42295807363261392859378435913 : (((p2 ∧ ((p3 ∨ (False ∧ ((False → (p4 ∧ (False ∧ p5))) → (((p4 ∧ (p3 ∧ p4)) ∨ ((p2 → p1) → p3)) → p5)))) ∨ p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356041897304456636722423910600 : (p5 → ((False ∧ (p5 → (((p5 ∧ p3) → p1) ∧ (((p4 → p1) → (p5 → (p2 ∨ p1))) ∧ (p1 ∨ p5))))) ∨ (p4 ∨ (p4 → (True ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662027855074754403119400786312 : (((((p5 ∨ (p4 → (p5 → (p1 ∨ ((p4 → ((p3 ∧ p4) ∨ True)) ∧ p4))))) → (False ∧ ((p5 → (p5 → p2)) → p4))) → (p5 ∧ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p4 → (p5 → (p1 ∨ ((p4 → ((p3 ∧ p4) ∨ True)) ∧ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ (p4 → (p5 → (p1 ∨ ((p4 → ((p3 ∧ p4) ∨ True)) ∧ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157601968142428950187212217573 : (((p4 → (((((False ∨ False) ∨ p4) ∨ p3) → p2) ∨ ((False ∨ (False → p3)) ∨ p2))) → (p2 ∨ True)) ∨ (p2 → (((p3 ∨ p5) ∨ p3) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48098206985658671689746233346 : ((((p5 ∧ ((True ∨ p5) → p4)) ∧ (True → ((((p3 ∨ ((p4 → p2) → p2)) → p2) ∧ (True ∨ (p3 ∨ p2))) → p4))) → (True → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64719066176104962866913646934 : ((p1 ∨ (p3 → (p2 ∨ (p1 → ((p5 ∧ (((p3 ∧ (p2 → p5)) → p5) ∧ p2)) ∨ (False → ((p2 ∨ p2) → ((p1 → p4) ∨ p1)))))))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196416960963267059894385052009 : ((True → (False → (((p4 → False) ∨ True) ∨ p3))) ∧ (((p1 → (((p3 ∨ False) → True) → p2)) ∧ p4) ∨ ((p4 ∨ p5) ∨ (p3 → (True ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55934281759702253204768255239 : (((p2 → ((False → True) ∨ p1)) ∧ (p1 ∧ ((False → ((True → (p4 → p4)) ∨ (p4 ∧ (p4 ∨ p1)))) → (((p2 ∨ False) → p5) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246663553312585110761119349508 : ((p5 ∧ p3) ∨ (p3 ∨ (((((p2 → True) → p3) ∧ (p3 ∧ True)) ∧ (((((p2 ∧ p1) ∧ True) ∨ p3) → p4) ∧ (p5 ∧ (p4 → p1)))) → p1))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p4 := by
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : (((p2 ∧ p1) ∧ True) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50767406561676962935394725913 : (((False ∨ ((((p2 ∨ p5) ∨ p1) ∨ p1) ∨ (((p3 ∨ (p2 → p1)) → (p4 ∧ (False ∨ p3))) → p3))) → ((p4 → (p4 → True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300079272893265235157405886017 : (False ∨ ((((True → p2) → ((p3 ∧ ((((True ∧ True) → False) → False) ∨ p4)) → ((True ∨ p4) → (False ∧ (p2 ∨ p5))))) → p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148913832933294266021241970310 : ((((p1 → (p4 → p4)) ∧ p1) → (((((p2 ∧ False) ∨ (p2 ∧ False)) ∧ p5) ∧ (p5 ∨ p3)) ∨ (p5 → True))) ∨ ((p1 ∨ p5) → (p2 ∨ p5))) := by
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
theorem thm_5_vars_790016587634128559791457318633 : (((p5 ∨ ((p2 ∧ p3) ∨ (p1 ∧ ((p5 → False) → (((p5 ∨ p5) ∧ p1) ∧ ((p4 ∧ ((p2 → ((False ∨ False) ∧ p1)) ∧ False)) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341283502270439220529177603727 : (p2 → ((((((False ∨ ((p1 → (p1 ∨ (p5 ∨ p3))) → False)) ∧ ((True ∨ p3) ∨ p4)) ∧ p3) ∧ p5) ∧ (p4 → ((p3 ∨ p2) → p5))) → p4)) := by
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
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h15 : (p1 → (p1 ∨ (p5 ∨ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h17 := h12 h15
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h19 : (p1 → (p1 ∨ (p5 ∨ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h21 := h12 h19
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587115067226744066024078825621 : (((((p2 → ((p2 ∧ ((((((p3 ∧ p5) ∧ False) ∨ p2) → p4) → p4) ∨ (p1 ∨ ((p4 → (p1 ∨ True)) ∨ False)))) ∨ p5)) ∧ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301516095060702331194780372699 : (False ∨ ((p5 → (p5 ∧ True)) ∧ (((False ∧ (p3 → ((False ∧ p3) ∨ (p4 ∨ ((p3 ∨ True) ∨ p3))))) ∨ (p5 ∨ (False → (True → p1)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136393786465320178672061060681 : (((p4 ∧ ((p4 ∧ p1) ∨ False)) ∨ ((p2 ∨ ((((((p2 ∨ True) ∧ True) ∨ True) ∨ (p5 ∨ p4)) ∨ p1) → False)) ∨ p3)) ∨ (p2 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610485196257840555622856478229 : ((((((p1 ∨ ((p3 ∧ p5) ∧ (p5 ∧ (p2 → (p1 → (False → (p1 → ((p1 ∨ ((p1 → p1) ∧ p2)) → False)))))))) → p4) → False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166319874727847011036409157840 : ((p5 ∧ ((((p1 → ((((True → p2) → p5) → p5) ∨ False)) ∧ p4) ∧ p5) → (p4 → p1))) ∨ ((p1 → (((p1 ∧ p2) ∨ p1) ∨ p4)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113136959096446032685900225628 : (((p2 → ((p5 ∨ (p5 ∨ (p2 ∧ (p4 → ((p4 ∧ False) → p3))))) ∨ ((p2 ∨ (p4 ∧ ((p1 ∨ True) ∨ p3))) ∧ p2))) → p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46908063736323955203075599672 : ((((((p3 ∨ (False ∧ p5)) ∧ (((p4 → p1) ∧ ((False ∧ p5) ∨ (p4 → p4))) ∧ True)) → (p1 → (p4 → p2))) ∨ p5) ∨ (p5 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174282088590713942274173785568 : (((p2 ∧ (((True ∨ (True ∨ p3)) → p4) ∨ (p1 ∨ p1))) ∧ (p2 ∧ (p3 → p5))) → (p5 ∨ (p4 ∨ ((p4 → False) → (p3 → (True ∨ p2)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (True ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769980254907548922631138544359 : (((p5 ∧ (p1 → ((p4 ∨ (p5 ∧ (p3 ∧ False))) → ((((False ∧ p2) ∨ p1) ∧ ((p3 ∧ (p4 ∨ (p1 ∨ p1))) ∨ (p1 ∧ p5))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619339354209866818035123578648 : ((((((False ∧ p2) → p3) → ((p4 → (p4 ∨ ((p3 ∧ (((p1 ∨ p5) → ((False ∧ p5) ∧ p1)) ∨ p3)) → (p4 ∨ p3)))) → False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663027223601624342873708647820 : (((((p5 ∧ (p5 → p1)) → (p5 ∨ (((p3 ∨ p4) → p5) ∨ ((((p5 ∧ False) → (p1 ∧ (p4 → True))) ∧ False) → True)))) → (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64056919002963663621220749929 : ((False ∨ (((((p4 ∨ p1) ∨ (p1 ∨ p3)) ∨ (False ∨ (p2 ∧ (True ∧ p2)))) ∨ ((p5 ∨ p5) → True)) ∨ (p3 ∨ ((False ∨ p4) ∧ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_56222039869028352965524796400 : (((p2 ∨ (p5 → (p1 ∧ p5))) ∨ (((((p2 → (((p2 → p2) ∨ p2) ∨ p3)) → (((p4 ∨ True) ∨ True) → p1)) ∨ True) ∧ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636730388603100093702979793130 : (((((p5 ∧ (((p3 → False) ∨ (((True ∨ p5) ∨ (p4 → False)) ∨ p5)) ∧ p3)) ∨ (True ∨ ((((p3 ∧ p2) ∨ p2) ∧ p3) → True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354039762073428530893383456264 : (p4 → (p4 → (((((p5 ∧ p4) ∨ (p1 ∧ False)) → ((p1 → (False ∨ True)) → p3)) ∧ p4) → ((p3 ∨ ((p4 ∧ p1) ∨ (p5 → p5))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51799586797821761836520082157 : (((p1 ∨ (p5 ∨ (False ∧ (((True ∨ (False ∧ False)) ∧ p3) ∨ (p4 ∨ (p5 ∧ p5)))))) ∧ (p4 → ((False ∨ (p5 ∨ (p5 ∨ False))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245360526772964471792848973832 : ((p2 ∧ p3) ∨ (((p2 ∧ ((((p3 → p4) ∧ (p3 ∨ p4)) → p4) → p4)) ∨ (p2 ∧ (True → (False ∨ p3)))) ∨ (((p2 ∧ True) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120116908994682856544586853740 : (((((True → p2) ∧ p2) ∧ ((((((p4 → ((p4 → p1) ∧ p4)) → False) ∧ p5) → p5) ∨ (True ∧ True)) → (False → p3))) ∧ True) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750769593930936937937325066391 : (((True ∧ ((((((False ∧ p3) ∧ (False ∨ True)) ∨ (p4 ∧ p3)) ∨ True) ∧ p3) ∨ (p2 ∧ (p3 ∨ (p2 ∧ (p5 ∧ (p1 ∨ (p2 ∧ p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671434614765338615738754392843 : ((((p1 → (p3 ∨ ((((p2 ∧ p4) ∨ p3) ∨ (p1 → ((((p5 ∧ p5) ∧ p4) ∨ p5) → (False ∧ p2)))) ∨ p5))) ∨ (True ∧ (False → False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47150194101156906957838460051 : ((((p5 ∧ ((((True → p4) ∧ (False ∧ (p4 → (p1 ∨ p1)))) ∨ p3) ∧ (p5 → True))) ∨ (p5 ∨ ((p5 ∧ p3) ∧ p1))) ∨ (p1 → p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217130187371660168465864615744 : ((((p5 ∨ p4) ∨ p4) ∨ p2) → (((((p1 → p1) ∨ True) → (((p2 ∨ False) → p4) ∨ ((p2 ∧ p3) ∨ True))) ∨ ((p5 → p1) ∧ True)) ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149357704999762092951262663228 : (((p5 ∨ p1) → (p1 → ((((p4 ∨ (p4 ∨ ((p4 ∨ p2) → True))) ∨ (p4 ∨ p5)) ∧ (False ∨ p1)) ∨ p3))) ∨ ((p5 → p2) ∧ (p4 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110411834061471944090087930351 : ((p3 → ((p2 → ((True ∧ True) ∨ p1)) → ((p5 → (((False → ((p5 ∨ True) ∨ ((p4 ∨ p5) ∧ False))) → p1) ∨ p3)) ∨ p4))) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248259983051726419025092325919 : ((p2 ∨ p2) ∨ (((p4 ∨ p5) → ((p1 → (((((((p5 ∨ p4) ∨ False) → True) → (p5 ∨ p2)) ∨ p4) → p1) → p1)) → (p2 ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40938691816894278297578629840 : (((((False ∨ ((p4 ∨ ((p2 ∧ (False ∧ ((True → False) → (p5 ∨ p2)))) ∧ (p5 ∨ (p3 ∨ p4)))) ∨ True)) ∨ p3) ∨ (p3 ∧ p5)) ∨ p1) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336138479066347618850829735725 : (p1 → (((p2 ∨ ((False ∧ (((False ∨ (p2 → (False → p1))) ∨ (((p3 ∨ p5) ∧ (False → p3)) ∨ (p3 ∧ False))) → p2)) ∧ p4)) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322270845280034793269917377693 : (p5 ∨ (((p4 ∨ (p1 → ((True ∨ p3) → (((((p4 → (p2 ∧ True)) ∧ ((p1 ∨ p4) ∧ False)) ∧ p1) ∨ (p3 ∧ p4)) ∨ p3)))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117076602748310926863113747620 : (((True → p5) → ((True ∧ (p2 ∧ p2)) → ((((((p5 ∨ p5) → p3) → False) → p1) ∧ ((p1 ∨ p5) → p5)) ∨ (p5 ∨ p5)))) ∨ (p3 ∧ p4)) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340794007045631491493686404100 : (p2 → ((((p1 ∨ p3) ∨ (False → (True → ((((p1 ∨ p1) ∨ (p4 → (p5 ∨ ((p3 ∧ p2) → p2)))) ∨ (p2 → p2)) ∨ True)))) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112460285146597804383781107419 : (((((p4 ∧ ((True ∧ ((p5 ∨ (False ∨ False)) → (p1 → (True → p5)))) → p3)) → ((p3 ∧ p4) → (p3 ∨ p4))) ∨ True) → False) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151802088968421310017597308614 : (((((p3 → ((True ∧ False) → (False ∨ True))) ∨ (p2 ∨ (p1 ∧ p5))) ∨ False) ∧ (p4 → ((p4 ∧ p2) ∨ True))) → ((True → p2) → (p1 ∨ p2))) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358257828962956866434472477419 : (p5 → (p4 ∨ (p5 ∧ (((p3 ∨ ((p1 → True) ∧ (((((p4 ∧ p2) ∧ True) ∨ (p2 ∧ p2)) → (p1 ∨ (False ∨ p2))) ∨ False))) → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105141146041832347481195394765 : ((((((p4 ∨ True) ∧ (p3 → p5)) ∨ p3) ∧ (p1 → ((((p5 → p5) → False) → (False ∧ p1)) ∧ p4))) ∨ ((p3 ∧ p5) → True)) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758730670964606365763730082720 : (((p2 ∧ ((False ∧ ((False → p3) ∧ (((p1 → (p1 → (True ∨ ((p5 → (p5 → False)) → False)))) → p2) → (p1 ∧ (p5 ∨ p5))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_574755343822778560324508164805 : (((p2 → (((True → p3) → ((False ∨ ((p4 ∨ ((p1 ∨ p5) ∨ True)) ∨ p3)) ∨ False)) ∧ (((p3 → False) → (False ∨ (p3 → p5))) ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200599691364460711652270017755 : ((True ∧ (p1 ∨ (True ∨ (p4 ∧ (p1 → p2))))) → (((p2 → (True ∧ p1)) ∧ p4) → (((p3 → (p1 → p3)) → ((p2 ∧ p1) → p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49650191621308405696296127533 : ((((p3 ∧ (p2 ∨ (p3 → False))) → ((p2 → (((p3 ∨ p4) ∧ (p3 ∧ p2)) → (True ∧ (True ∨ True)))) ∨ p1)) → (False ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112176153428378550209966371010 : (((p4 ∧ ((((True ∨ (((p1 → p1) ∧ (p3 ∧ p3)) → (p4 → (p4 ∨ False)))) → (p5 ∨ p2)) ∨ p2) ∨ (p5 ∨ True))) ∨ p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183794782586120335788984343477 : (((((p5 ∨ (p3 ∧ ((True → p5) → p3))) ∨ False) ∨ p3) ∧ False) ∨ ((p2 ∨ True) ∨ (((((p2 ∨ True) → p4) ∧ (p4 ∨ p5)) → p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165709408239344452558908593050 : (((((p3 ∧ False) ∨ p2) → p5) ∧ (((True ∧ p5) → (((True ∨ False) → p1) → p2)) ∧ False)) ∨ ((p1 ∨ (p5 → True)) ∨ ((p4 → p1) ∨ p2))) := by
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
theorem thm_5_vars_636121760221408755685690491332 : ((((((((True ∧ p2) → (((False → True) → (p2 ∨ True)) ∧ p2)) ∨ (p3 ∧ p3)) ∨ p5) ∨ (p1 ∨ (p3 → (p1 → (p5 ∧ p5))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_930981942131395444224473153524 : ((((((p2 ∨ p4) ∧ p1) → ((p1 → (p4 ∧ False)) → False)) → (p1 ∧ ((p1 → ((p3 → p5) ∧ (p5 → (True ∨ p3)))) → (p4 ∨ p3)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ p4) ∧ p1) → ((p1 → (p4 ∧ False)) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45085608246341371430368832850 : ((((p3 ∧ p1) → (p5 ∧ (p4 → ((p2 ∨ (p5 ∨ p1)) ∨ ((((p3 ∧ p2) → p4) → ((p1 ∧ p3) → (p1 ∧ True))) ∨ p3))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113637247757896854528465910481 : (((p5 → (((p1 ∧ p3) ∨ p5) ∧ (p3 ∨ (((False ∨ p1) ∧ ((True ∧ (p4 ∧ p1)) → p1)) ∨ (True ∧ True))))) ∨ (p1 ∧ p2)) ∨ (p3 ∧ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667561176742325087633823508117 : ((((p1 ∧ (((True ∨ (p1 → (False ∨ (p5 → ((p3 ∧ p1) ∨ (p4 ∨ (p4 ∨ True))))))) ∨ p4) → (p1 → p5))) ∧ ((False → True) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37561568138230379216669497620 : ((((p3 ∨ ((False ∨ (p1 → (p5 ∨ ((((((True → p3) ∨ p1) ∨ False) ∨ p5) ∨ (p5 ∨ False)) ∧ p2)))) → (p2 ∨ p5))) ∨ False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213291321702638224431681233644 : ((((p3 → p5) → False) ∧ p2) ∨ ((((False ∧ (p1 ∧ (True → p5))) ∨ p4) → ((((p3 → (True → (False ∨ p3))) → False) ∧ p5) → p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → (True → (False ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h9
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172875566936728616938370427565 : ((p1 ∧ (((((True → (p5 ∨ p5)) ∨ p5) ∨ (p2 → p3)) → True) → (p5 ∧ True))) ∨ ((True ∧ p3) ∨ (p2 ∨ ((False ∧ (True ∧ True)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_660243601129357372062040837599 : ((((((p1 → p4) ∧ (((p4 ∧ (((True ∧ (True ∨ ((p3 → True) ∨ p2))) ∧ (False ∨ p5)) → p3)) ∨ p5) ∨ False)) ∨ p4) → (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313763573691891686240113150848 : (p3 ∨ ((True → (((((((p3 ∧ (False ∧ p4)) ∨ p4) → (p4 ∨ p1)) ∧ p4) → p2) ∨ p2) ∧ (((True ∧ p5) ∧ (p2 ∧ False)) ∧ p3))) → p2)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114663629898263039702005527522 : ((((p4 ∨ (p1 ∨ p2)) ∨ ((p2 ∧ (False ∨ p1)) ∨ ((p3 → p2) → (p2 → p2)))) ∨ (((p2 ∨ (p4 → p1)) → p2) → True)) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708215019105756382639752976076 : ((((p2 → (p4 → (p5 ∨ (False ∨ (p1 ∨ False))))) ∨ (p3 → (p5 ∨ ((((((p5 → p3) ∧ p1) → p4) → p4) → p3) → (p2 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354885069442432542559449452556 : (p5 → ((p2 ∧ ((p1 ∨ (p3 → p4)) ∨ ((((True → p5) → p3) → p2) ∨ (p1 → (((p3 → (p1 ∨ p3)) → (p3 ∨ p4)) → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136850282800599674122288644073 : (((p3 ∧ p5) ∨ (p4 ∨ (p4 ∨ ((p3 → (True ∧ (((p2 ∧ p2) ∨ (p3 → True)) ∨ ((p4 → p3) ∧ p2)))) ∨ False)))) ∨ (p5 ∨ (p2 ∧ p5))) := by
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
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218187569097917242854710525255 : (((p1 ∧ p2) ∨ (p2 → p3)) → (((((((True → p5) ∨ ((p2 ∧ p4) → p3)) ∧ (p3 → False)) ∨ (p5 → p2)) ∨ (p5 → True)) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137914453328359550009141635317 : ((p4 ∨ (((False ∧ True) ∧ p5) ∨ (((False ∨ p2) ∨ (p5 ∧ p1)) ∨ (p2 → (((True ∨ p4) → p2) ∨ (p4 ∨ p3)))))) ∨ ((p4 ∨ p4) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136452112725261150248447581774 : (((p1 ∨ ((p3 → p1) ∨ p2)) → (p2 → (((True ∧ p5) ∨ (True ∨ (p1 ∨ p5))) → (False ∨ ((False ∧ False) → False))))) ∨ (False ∧ (p5 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    cases h1
    case inl h7 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- False on the left can always be used.
          apply False.elim h29
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- False on the left can always be used.
          apply False.elim h33
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h38
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- False on the left can always be used.
          apply False.elim h39
        case inr h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h43
            -- Conjunctions on the left can always be decomposed.
            let h44 := h43.left
            let h45 := h43.right
            -- False on the left can always be used.
            apply False.elim h44
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h47
            -- Conjunctions on the left can always be decomposed.
            let h48 := h47.left
            let h49 := h47.right
            -- False on the left can always be used.
            apply False.elim h48
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h52
          -- Conjunctions on the left can always be decomposed.
          let h53 := h52.left
          let h54 := h52.right
          -- False on the left can always be used.
          apply False.elim h53
        case inr h55 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h56 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h57
            -- Conjunctions on the left can always be decomposed.
            let h58 := h57.left
            let h59 := h57.right
            -- False on the left can always be used.
            apply False.elim h58
          case inr h60 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h61
            -- Conjunctions on the left can always be decomposed.
            let h62 := h61.left
            let h63 := h61.right
            -- False on the left can always be used.
            apply False.elim h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147619372963605201553470940057 : (((((True ∧ (((((p4 ∨ (p4 ∨ True)) → (p1 → p5)) ∨ False) → (p4 ∨ p2)) ∨ False)) ∧ True) → p1) → False) ∨ (False → (p2 → (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204313386206890429053985153369 : (((p1 ∧ (True ∧ (p2 ∧ p3))) ∧ True) ∨ ((p5 → ((p4 → p2) ∧ p4)) ∨ (p2 → ((p3 ∨ (False → p3)) ∧ (p2 → ((p2 → p3) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180340015507989628051966351116 : (((p2 ∨ (p5 ∨ (((p3 ∨ p4) ∧ (True → p5)) ∧ p3))) ∧ (p5 → p1)) → ((p5 ∧ (((p4 → False) → p2) ∧ p5)) ∨ (p4 ∨ (False → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41406160745573849051236825086 : (((((p4 ∨ (((True → ((p3 → p2) ∧ False)) ∨ (p3 ∨ p5)) ∨ p1)) ∨ p5) ∨ ((p4 ∧ ((p5 ∨ p2) ∨ (p3 ∨ p2))) → False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64918803072356313207305198219 : ((p2 ∨ ((((p5 → True) ∨ ((p1 ∧ (p1 → p3)) ∨ ((p3 ∧ (False ∧ p4)) ∨ False))) → p2) ∨ (((p5 ∨ (p4 → p3)) → p1) → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248835675672313805071493174594 : ((p3 ∨ p4) ∨ ((p1 ∧ (p4 ∧ p3)) → (p1 → ((p2 ∧ (p5 ∧ False)) ∨ ((p2 ∨ (p3 ∧ p1)) → ((((p3 ∨ True) ∨ p2) ∧ p4) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762007348641532059270777131027 : (((p3 ∧ ((False ∨ (((p3 ∧ (p5 ∨ p5)) ∧ p5) ∨ (((((False ∨ ((p2 ∨ p2) → p4)) ∨ p4) ∨ True) ∧ (False → False)) ∧ p1))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



