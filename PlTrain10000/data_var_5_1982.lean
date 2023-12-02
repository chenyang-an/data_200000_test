variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181127775331530983673491631507 : ((True ∧ (p3 ∧ (((p3 → True) → (((False ∨ p5) → True) ∨ p3)) ∧ p5))) → (((((p3 ∨ p2) → (p2 → (p2 ∧ p1))) ∧ p1) ∧ p3) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187316876690366155783513580564 : ((p1 ∧ (p5 ∧ (p2 ∨ (p3 ∨ (True ∨ ((p3 → True) ∧ False)))))) → ((p2 → ((p5 ∧ p3) ∧ (p3 ∨ (p5 → ((False ∧ p1) ∨ False))))) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737974577382802360250180904401 : ((((True ∧ p4) ∨ ((p1 ∨ p3) ∨ (False ∧ ((((((p3 ∨ (p1 → (p5 → (p5 → False)))) ∨ (False ∨ p3)) ∨ False) → True) ∨ False) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218592668593775514739979997117 : (((p3 → p1) → (p1 ∧ p4)) → ((((((False ∧ (p2 ∨ (p4 ∧ p5))) ∨ (p3 ∨ True)) ∧ p3) ∧ p4) ∨ ((p3 → p3) ∧ (False → p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112829146732685141904878638850 : ((((p1 ∧ ((p4 ∨ p3) ∧ p1)) ∨ (((p5 ∧ (p4 → True)) ∧ (p4 → (((p4 → False) → p1) → p4))) ∨ (p1 → p4))) → p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788203051145121406820538449286 : (((p5 ∨ (((p2 ∨ p4) → ((p3 ∨ (((((p4 ∨ True) → p3) ∧ p3) → p5) ∧ ((p4 ∨ (p5 ∧ (p1 ∨ p4))) ∧ p5))) → p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680184495736324043002321032249 : ((((((True ∨ (p5 ∧ (p3 ∧ p5))) ∧ ((p2 ∧ (((p2 ∨ p5) ∨ p4) ∧ True)) ∧ p3)) ∨ (p3 ∨ p3)) → ((p2 → p5) → (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595643314828644736372464316284 : ((((((p4 ∨ p2) ∧ (p5 ∨ (p5 ∨ (p2 → (p3 → (p1 → p5)))))) → ((True ∧ (p1 ∨ (p5 → False))) ∨ ((p3 → p3) ∨ False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341962877203645283679720095994 : (p2 → (((((p5 ∧ p3) ∧ p4) ∨ (((p4 ∧ p2) → (p5 ∧ ((p2 ∨ p1) ∧ (p4 ∧ p3)))) ∧ (p2 ∨ p1))) ∧ p3) ∨ (p4 ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_724453899206434317913310985639 : ((((True ∨ (p5 ∨ p2)) ∧ ((p1 ∧ p3) ∨ (p5 → (p3 ∧ (p5 ∧ ((((False ∧ ((False ∨ p1) → p3)) → p5) → (True ∧ False)) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114772850637657000792120900755 : ((((((((p2 ∧ p4) ∨ p5) ∨ p5) ∨ True) ∨ ((p4 ∨ p1) → False)) ∧ True) ∧ ((((False ∧ p3) ∨ p4) → p5) → (p1 ∨ p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682648440026973097762814087239 : ((((((p3 → (p4 ∨ p3)) ∨ (p5 → True)) ∧ (p3 ∨ ((((p1 → False) ∧ False) ∧ p5) ∧ p3))) ∧ (((p1 ∧ (False ∨ False)) ∧ p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42514724319846624923956832254 : (((False ∨ (False ∧ (((True ∨ p3) ∨ ((p1 ∧ (p2 → (False ∧ (p5 → p2)))) ∨ ((p2 ∨ (p5 → False)) → (True ∨ p3)))) → False))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255848072282489084468569225999 : ((True ∨ p1) → ((((p1 → p3) ∧ ((p5 ∨ p1) ∨ (((((p4 ∧ p1) ∧ p5) → ((False → True) → (p1 ∧ p2))) ∨ p3) ∨ p2))) ∨ True) ∨ p5)) := by
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
theorem thm_5_vars_914262071546736631525058043505 : ((((((((((p4 ∧ True) → p4) → p1) → (p4 → p2)) ∨ p5) ∧ p5) ∨ (p1 → p2)) ∧ (((p1 ∨ (p2 ∧ (False ∨ p1))) ∧ p5) ∧ p2)) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- One of the premise coincides with the conclusion.
        exact h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258897187764979863012428046469 : ((True → p2) → (((p1 → (p3 ∨ ((((p4 ∧ p3) ∨ (p2 → p3)) ∧ p5) ∨ (False ∧ p4)))) ∨ (True ∧ ((True → p3) → p1))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330539267562018647853835607177 : (True → (p5 ∨ (((((((p4 → p2) ∧ p3) ∨ (True ∧ False)) ∧ p5) ∨ (((False ∧ p1) → False) ∧ (p3 ∨ p3))) ∨ ((False ∧ True) ∨ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_164494634956627287218493395356 : (((((False ∨ (((p1 ∨ p1) → (True ∧ p5)) ∨ p3)) ∨ (p3 ∨ (True → True))) → p3) ∧ False) ∨ (p2 → (True ∧ (((p2 ∨ p4) ∨ False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694718394870581202200109419900 : ((((p2 ∨ (p3 → (((p3 ∧ p1) ∨ ((p2 → p5) ∧ (p2 → p5))) → p4))) ∨ ((False → (p2 ∧ p5)) ∨ (p5 ∨ ((p3 → p2) ∧ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52716043540041837297092115729 : ((((((((p4 ∧ p2) → p2) ∨ (p3 ∧ False)) → p3) ∧ (True ∧ p3)) ∧ p3) → (((p1 ∧ p3) ∨ (p2 → (False ∧ p5))) ∧ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52899859355561638251602729210 : (((True → (((True → p2) ∧ (p3 → p4)) ∧ ((False → (True → p4)) ∨ p3))) → (p2 → ((p1 ∨ (p2 → p5)) → (False ∧ (False ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54412754459984443899901761789 : ((((p4 ∨ (p1 ∨ ((p1 ∨ p2) ∧ False))) ∧ False) ∨ ((p4 ∧ ((((True ∧ p3) ∧ ((p5 → False) → (p5 ∧ p3))) ∨ p3) ∧ True)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306249552993471748060012459422 : (p1 ∨ ((p5 ∧ (False ∨ p3)) → (((p3 ∧ (p5 ∨ p3)) ∨ True) → (((p1 → p3) → ((p5 ∧ (p2 → p3)) → False)) → (False ∧ (p1 ∨ p1)))))) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h12
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (p5 ∧ (p2 → p3)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h8
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h23
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : (p5 ∧ (p2 → p3)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h19
          -- Implications on the right can always be decomposed.
          intro h27
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h28 := h25 h26
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h34 : (p1 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h36 := h3 h34
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h37 : (p5 ∧ (p2 → p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h30
        -- Implications on the right can always be decomposed.
        intro h38
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h39 := h36 h37
      -- False on the left can always be used.
      apply False.elim h39
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h1.left
      let h45 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h48 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h49
          -- One of the premise coincides with the conclusion.
          exact h47
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h50 := h3 h48
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h51 : (p5 ∧ (p2 → p3)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h44
          -- Implications on the right can always be decomposed.
          intro h52
          -- One of the premise coincides with the conclusion.
          exact h47
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h53 := h50 h51
        -- False on the left can always be used.
        apply False.elim h53
    case inr h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h1.left
      let h56 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- False on the left can always be used.
        apply False.elim h57
      case inr h58 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h59 : (p1 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h60
          -- One of the premise coincides with the conclusion.
          exact h58
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h61 := h3 h59
        -- We want to use the implication h61 based on <expert-advice>. So we show its premise.
        have h62 : (p5 ∧ (p2 → p3)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h55
          -- Implications on the right can always be decomposed.
          intro h63
          -- One of the premise coincides with the conclusion.
          exact h58
        -- We have shown the premise of h61, we can now drive its conclusion.
        let h64 := h61 h62
        -- False on the left can always be used.
        apply False.elim h64
  case inr h65 =>
    -- Conjunctions on the left can always be decomposed.
    let h66 := h1.left
    let h67 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h67
    case inl h68 =>
      -- False on the left can always be used.
      apply False.elim h68
    case inr h69 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h70 : (p1 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h71
        -- One of the premise coincides with the conclusion.
        exact h69
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h72 := h3 h70
      -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
      have h73 : (p5 ∧ (p2 → p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h66
        -- Implications on the right can always be decomposed.
        intro h74
        -- One of the premise coincides with the conclusion.
        exact h69
      -- We have shown the premise of h72, we can now drive its conclusion.
      let h75 := h72 h73
      -- False on the left can always be used.
      apply False.elim h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719459898396759136522071770170 : ((((p1 ∨ (p5 ∧ (False ∨ p2))) ∨ (((p2 ∧ True) → ((p2 ∨ (p4 ∨ False)) ∧ (True ∧ (p3 ∨ ((False ∨ p4) ∨ p5))))) ∧ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64494564355657744856487429819 : ((p1 ∨ (((p1 ∧ (p2 ∧ (p4 ∨ (False ∧ p4)))) ∨ (p3 ∨ (p3 → (True → (p2 ∨ p5))))) ∨ ((p5 ∨ (False ∨ (False ∨ False))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56816399945695349510875372342 : ((((p5 ∨ p4) → p1) ∧ (p5 ∧ (p1 ∧ ((((p3 ∧ p3) ∧ (False ∨ (False ∧ (False → (p4 ∧ p2))))) ∨ (False ∧ p4)) ∧ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148961111515402725288607043067 : ((((True ∨ p3) ∨ p1) ∧ (p1 ∨ (p1 ∧ (((p1 → ((p3 ∧ (True ∧ p4)) ∨ True)) → False) ∨ (True ∧ p2))))) ∨ ((p3 → (False ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711215463301803586996803345559 : ((((p4 ∧ (((p4 → p2) ∧ p5) ∧ p2)) ∧ (p3 ∧ (((p5 ∧ (p2 → ((p1 ∨ p2) ∨ (False ∧ p4)))) → (p4 ∧ (p5 ∧ p5))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_500318855640003758779456211687 : (((((p3 ∨ True) → False) ∨ ((True → p2) → (((p5 ∧ p3) ∨ (((((p2 ∧ (p1 → p1)) ∨ True) → p3) ∧ p3) ∧ (p5 ∨ p2))) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141900190850022426215480987362 : (((p4 → p2) ∨ (((p5 ∨ p2) ∧ (p5 ∨ ((p1 ∨ p2) ∨ ((p4 ∨ False) ∧ (p1 ∧ p4))))) ∧ (p5 ∨ (p5 ∧ False)))) → (p1 ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
        cases h5
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h17 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h16
            case inr h18 =>
              -- Conjunctions on the left can always be decomposed.
              let h19 := h18.left
              let h20 := h18.right
              -- False on the left can always be used.
              apply False.elim h20
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h23 =>
              -- Conjunctions on the left can always be decomposed.
              let h24 := h23.left
              let h25 := h23.right
              -- False on the left can always be used.
              apply False.elim h25
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h28.left
            let h31 := h28.right
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h32 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h30
            case inr h33 =>
              -- Conjunctions on the left can always be decomposed.
              let h34 := h33.left
              let h35 := h33.right
              -- False on the left can always be used.
              apply False.elim h35
          case inr h36 =>
            -- False on the left can always be used.
            apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- False on the left can always be used.
          apply False.elim h42
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- Disjunctions on the left can always be decomposed.
          cases h44
          case inl h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h46 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h45
            case inr h47 =>
              -- Conjunctions on the left can always be decomposed.
              let h48 := h47.left
              let h49 := h47.right
              -- False on the left can always be used.
              apply False.elim h49
          case inr h50 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h51 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h52 =>
              -- Conjunctions on the left can always be decomposed.
              let h53 := h52.left
              let h54 := h52.right
              -- False on the left can always be used.
              apply False.elim h54
        case inr h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h58 =>
            -- Conjunctions on the left can always be decomposed.
            let h59 := h57.left
            let h60 := h57.right
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h61 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h59
            case inr h62 =>
              -- Conjunctions on the left can always be decomposed.
              let h63 := h62.left
              let h64 := h62.right
              -- False on the left can always be used.
              apply False.elim h64
          case inr h65 =>
            -- False on the left can always be used.
            apply False.elim h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264625416001427676323546866832 : (True ∧ (((False ∨ p1) → p4) → ((((((((False ∧ False) ∨ p4) ∧ p2) ∨ p4) ∨ True) ∨ (((False → True) → p5) ∧ p5)) ∨ p4) ∧ (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37558267155566438119898840368 : ((((p2 ∨ (((True → p3) ∨ (p4 ∨ ((p4 ∨ ((p1 → p4) ∧ p1)) ∨ True))) ∨ (((p1 ∨ True) ∨ True) ∧ (p3 ∧ p4)))) ∨ p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191290328687139547010401176284 : (((True → False) ∧ (((True → False) ∨ p2) → (p4 ∨ p5))) ∨ (True ∨ (p1 ∧ (p5 → (p2 → (False → (p5 ∨ (p1 ∧ ((p2 → p1) ∧ True))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754479207481506599869628984097 : (((False ∧ (True ∧ (p3 ∧ (p2 ∨ (p1 ∧ (p2 ∨ ((False → p1) ∨ (p4 → ((p2 → ((p1 ∨ (True → p5)) ∨ True)) ∧ (p5 → p5)))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258686360190996563059511952508 : ((p5 ∨ p5) → (p1 ∨ (((p1 ∨ p3) ∨ (((((p1 ∧ True) ∨ False) ∨ (True ∧ (p2 → (p4 → p3)))) ∧ ((p5 → p5) → p5)) → True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116171830192504004180800606523 : (((p1 → (True ∧ p2)) ∧ ((((((p2 → True) → ((((True ∨ p4) → (p1 ∧ p4)) → False) → p3)) → p5) ∨ p2) → False) → p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47755180564356583496724380156 : (((((p3 ∧ p3) ∨ ((p4 ∧ (True → ((True ∨ ((((p1 ∧ (False ∧ True)) ∧ p4) → p5) → p4)) ∨ False))) → p4)) ∨ False) → (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178575386766529710885240731742 : (((p1 ∨ (p5 → (False ∨ (p3 ∧ False)))) ∧ ((p3 ∧ (False → p2)) ∧ p2)) ∨ ((p1 ∧ (p1 ∧ (p1 ∧ (p3 → (p4 → True))))) → (p4 ∨ p1))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149930873806675195776196932825 : ((p3 ∨ ((p3 → (((p4 → True) ∨ p2) → p3)) → (((p1 ∨ p2) → p4) ∨ ((True → p4) → (False → False))))) ∨ (True → (p2 → (p2 ∧ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96326557649568414494361358511 : ((False ∨ (((((p4 → ((p1 ∧ False) ∨ False)) ∨ p4) ∨ ((p1 → p1) ∧ (p4 ∨ (p3 → ((p3 → p5) ∨ (p4 → p4)))))) ∨ p3) → p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p4 → ((p1 ∧ False) ∨ False)) ∨ p4) ∨ ((p1 → p1) ∧ (p4 ∨ (p3 → ((p3 → p5) ∨ (p4 → p4)))))) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115491301576623558998338432419 : (((((p3 → ((p2 ∧ p4) ∨ p3)) ∨ False) ∨ p2) → ((p5 → p5) → (((True → ((p4 ∧ (p3 ∧ p3)) ∧ True)) ∨ False) → p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234383062962627652701824892811 : ((p1 → (True → p5)) → ((((True ∧ (p2 → (((p1 ∧ (p1 ∧ False)) ∧ False) ∨ False))) ∨ True) ∨ (p2 ∨ ((p1 → (p3 ∨ p3)) ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260238287054429431747471391289 : ((p2 → p3) → ((p5 ∨ ((True ∧ ((((p3 ∨ p4) → ((p2 → p4) ∨ p2)) ∨ True) ∨ p5)) → ((p4 ∧ p5) ∧ p1))) → (p5 ∨ (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∧ ((((p3 ∨ p4) → ((p2 → p4) ∨ p2)) ∨ True) ∨ p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805954276936099304762556103597 : (((p4 → (((p4 → ((False ∨ ((p3 ∨ (p3 → (False → p3))) ∨ False)) → ((True ∧ ((p1 ∧ p5) ∨ p2)) ∨ p1))) ∨ (False ∧ p5)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798591926276320227303279374039 : (((p1 → (((False → False) ∧ ((p5 ∧ p3) ∨ p3)) ∨ (p2 → (((p2 → True) ∨ p2) → ((p4 ∧ (((p2 ∧ True) ∧ p5) ∧ p3)) ∨ p2))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263568756280541167616150964199 : (True ∧ (((((p3 → p5) ∨ p3) → ((True → (p4 ∧ False)) ∧ p2)) → ((p3 ∨ p2) → (p4 ∨ (p5 → p4)))) ∨ ((p1 ∧ (False → False)) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_775248917038211764572650488493 : (((False ∨ ((p4 ∨ p5) → ((((((p2 ∧ p4) ∨ (p4 ∨ p4)) ∨ True) ∨ p4) ∨ (p5 → False)) ∧ (((p5 ∨ True) ∨ (False ∨ p3)) ∨ p4)))) ∨ p1) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63227122836172704319336169569 : ((p5 ∧ ((p4 ∧ (((p4 → p2) ∨ p5) → (p5 ∨ ((p3 ∨ (p2 ∧ p5)) ∧ True)))) ∧ (((p3 → p4) ∧ ((p2 ∧ p2) → True)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41608447721240486157577987223 : (((((p4 ∨ p2) ∨ (p4 ∨ ((p2 ∨ False) → p4))) ∨ ((p3 ∨ (((p5 → p3) ∧ ((True ∨ p2) ∨ p3)) ∧ p3)) → (p5 ∨ p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258309658996815707759215464778 : ((p5 ∨ True) → ((p1 ∨ (p1 ∨ p5)) → (((p2 ∨ p2) ∨ (p1 → (p2 → ((p1 → False) ∨ ((False → ((True ∧ p1) → p2)) → p1))))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206017911614103502381326471961 : ((p2 ∧ ((p4 ∧ (False ∨ False)) ∨ p1)) ∨ (((False → (p2 ∨ True)) ∨ ((p1 ∧ p3) → (p1 ∧ (p1 ∨ p1)))) ∧ ((p2 ∧ p1) → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344439242680189564739712158481 : (p2 → (p5 ∨ (((False ∨ False) → True) → (((((p5 ∨ p3) ∧ (((p1 → False) ∨ (p4 ∧ True)) ∨ (p5 ∨ (p4 → p4)))) ∨ True) ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257750913687604369852126644397 : ((p3 ∨ p4) → (((((p3 ∧ p3) ∧ True) → ((((p5 ∧ True) ∨ p2) ∧ (p4 → p5)) ∨ p4)) ∧ True) ∨ ((((True ∨ p1) ∧ p1) → True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302638124587022694790275015582 : (False ∨ (p2 ∨ ((p5 ∧ (p3 ∧ (p5 ∨ (p4 ∨ (((((p5 ∨ p5) → p5) ∨ p4) → p1) ∧ p3))))) ∨ (((p2 ∨ True) ∨ p5) ∨ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147560313326110146669363266222 : (((((p4 ∧ ((False → (p3 ∨ False)) ∨ (False → ((False ∨ p1) → (p4 → (p5 ∧ False)))))) ∨ p1) ∧ p1) → False) ∨ (p1 ∨ ((p1 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118527180230048713852943346502 : ((p3 ∨ ((p5 → p1) → (((p4 ∧ p2) ∧ (p2 → ((((p4 → True) → p3) ∧ p4) → p1))) ∨ ((p4 ∨ (True ∨ p3)) ∨ True)))) ∨ (p3 → p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58276812857962916234660653003 : (((True ∨ True) ∧ (((p1 ∧ ((p4 ∧ (p4 → True)) ∧ (p4 ∨ (((p4 → False) ∧ (p3 ∧ (p3 ∧ p2))) ∨ (True → p5))))) ∧ p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117829124417236652994694972376 : ((p4 ∧ (p5 ∧ ((((p3 ∧ p5) ∨ p5) ∨ p5) → ((((p1 → (p2 → p3)) ∧ ((False ∨ (p1 ∧ True)) ∨ p4)) ∧ False) ∨ p2)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160308327507543354791763098283 : (((((p3 ∨ ((p3 → (False ∧ p1)) ∨ False)) ∨ p4) ∧ (p4 ∨ (p5 ∨ (True → True)))) → (p5 → p4)) → (p4 → ((p4 → p1) → (True ∧ p1)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115008087775727636037769597397 : ((((False ∧ p4) ∧ (p1 → ((True ∧ p4) → ((p1 ∨ p5) ∨ p3)))) ∧ (p4 ∧ (p1 → (((p4 → p2) ∨ p4) ∨ (True → p2))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40586902634013536357635434856 : (((((((False → (True ∧ p1)) → (p4 ∨ p1)) → (False ∧ (p1 → ((p2 ∨ (p3 ∨ (p4 ∧ p5))) ∧ (True → True))))) ∧ p1) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340822560329380807650189032806 : (p2 → ((((((((p3 → p3) ∨ p2) ∨ (False ∨ p1)) → (p1 ∧ p2)) ∨ p1) ∧ (p4 ∧ (p2 ∧ (p1 ∨ (p1 → p3))))) ∨ (p2 → p2)) ∨ p3)) := by
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
theorem thm_5_vars_340899320878009531129928665079 : (p2 → ((((((p5 → (p3 ∨ p4)) → p4) ∨ False) ∧ (p5 → (p1 ∨ p2))) → ((True → (True ∧ (((p1 → p5) ∨ False) → p3))) ∨ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67846683022366394761759920429 : ((p2 → ((p4 → ((((((p4 ∧ p5) ∧ True) ∧ (p5 → p4)) ∨ (((p4 ∨ (p2 ∧ p1)) ∨ p4) ∧ p5)) ∨ False) → False)) ∨ (p2 → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354124662417229996086280507374 : (p4 → (p5 → (p3 ∨ ((((p3 ∧ True) → p5) → ((((p1 ∧ (p1 ∧ p1)) ∨ ((p1 → (p2 → p3)) ∧ p4)) ∨ True) ∨ (p5 ∨ False))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303747307402794170782331711217 : (p1 ∨ (((((((p2 ∨ ((((p2 ∧ (False ∧ p2)) → p3) ∧ ((p4 ∨ True) → p2)) ∨ True)) ∨ p3) ∨ (p3 → p4)) ∧ p4) ∨ p3) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139897264125073398484684820755 : (((((((p4 ∧ (p1 ∨ p2)) ∧ False) ∨ (True ∧ p2)) ∨ ((p4 ∨ (p4 → p2)) ∧ p5)) ∧ (True → p3)) ∧ (True → p2)) → (p2 ∨ (p4 ∧ False))) := by
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
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h24
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163231340961985568998909598043 : (((p2 ∨ (p3 → (False ∨ ((p1 ∨ p2) ∧ False)))) ∨ (((p5 ∧ p5) → (p1 ∨ p1)) → True)) ∧ ((p2 → p5) → (p3 → (True ∨ (True → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2105673511937055777707594579 : ((((p5 ∧ ((p3 ∨ p5) ∨ ((p5 → p5) → (p5 ∧ (p1 ∧ False))))) ∨ (p4 ∨ p3)) ∧ p4) → ((p2 ∨ ((p4 ∧ True) ∧ p4)) ∨ p2)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805153836517189066873740335806 : (((p3 → (p1 ∧ (p5 → (((False ∨ p2) → (False ∧ (((p5 → (p3 ∧ False)) ∨ ((p3 ∧ p1) → ((False ∨ p1) ∨ p3))) ∨ p3))) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154518812861683815346557912599 : (((((True ∨ True) ∨ p4) ∧ (((p2 ∨ (p3 → (p2 ∨ p2))) ∨ ((p4 ∨ True) ∨ p3)) → p2)) → p2) ∧ (((p4 ∧ p5) ∧ p1) → (p3 ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : ((p2 ∨ (p3 → (p2 ∨ p2))) ∨ ((p4 ∨ True) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : ((p2 ∨ (p3 → (p2 ∨ p2))) ∨ ((p4 ∨ True) ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 ∨ (p3 → (p2 ∨ p2))) ∨ ((p4 ∨ True) ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50295925316966695659258821975 : ((((((p2 ∨ p3) → ((p5 ∧ p2) → (p5 → (p3 → (False ∨ p3))))) → p5) ∨ (False ∨ (False → p3))) ∨ (((True ∧ p5) → p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647037965881471546915881298587 : ((((p3 → ((((p5 ∨ False) ∧ True) ∨ (p3 ∧ ((((p2 → (p3 ∨ p4)) ∨ p3) → (p1 ∧ (p4 ∧ p1))) → p5))) ∨ (p4 → p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39223659444821441027274365270 : (((True ∧ (True ∧ ((((False → p3) ∧ False) ∨ (p1 ∧ ((True ∧ p4) ∨ (p3 ∧ False)))) ∨ (((p4 ∧ p1) ∧ (False ∧ False)) ∨ True)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195273038473125261890600480380 : ((((p1 → (p4 ∧ p1)) ∧ False) → (p2 ∨ p3)) ∧ ((((p4 ∨ True) → (((p2 → ((p4 ∨ p5) ∧ p4)) ∧ p5) ∧ False)) → (p3 ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153154772021584675233714011451 : ((p5 ∧ (((((True → True) ∧ p5) → p2) ∧ ((True ∨ (p1 → (p5 ∨ p3))) ∧ (p1 ∧ (True ∨ p1)))) → p3)) → (p2 → (True → (p5 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346830804303046518944062604380 : (p3 → ((((p4 ∧ p2) ∧ (p5 ∨ ((p5 → True) → False))) ∧ (((p5 → p5) → (p4 ∧ p3)) ∧ (False → p4))) → (((p5 → p1) → p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h18 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h20 := h15 h18
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113260357158102463705974379739 : (((((p2 ∧ (((p3 ∨ False) ∧ ((p5 ∨ (p5 → (False ∧ p4))) ∧ p2)) → p5)) ∨ False) ∧ (p5 → (p1 → p4))) ∧ (True ∨ False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619740709152349027242793976399 : (((((True ∨ p4) ∧ (p2 ∨ ((((((p5 ∧ (True ∧ (p3 ∨ p3))) ∧ (p3 → True)) ∧ True) ∧ p5) ∧ p2) ∨ (p4 → (False → True))))) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115292012047884778514648184730 : ((((p4 → ((p5 ∨ (False ∨ p1)) ∨ (p3 → False))) ∧ p1) → (p3 ∧ ((True ∨ ((True ∨ (p1 → p1)) → False)) → (p4 ∧ p4)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68917829280620946073964990726 : ((p4 → (p1 ∨ ((p2 → ((p2 → (p4 → p1)) ∧ p2)) → ((((((p2 ∨ p2) ∨ True) ∨ (p2 ∨ False)) ∧ (p4 → p3)) ∧ p4) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604105280817567982579537532982 : ((((p5 ∨ ((p1 ∨ False) → (p1 → (((((p1 ∧ (False ∧ (p3 → (False ∧ p3)))) ∧ p1) ∧ (p3 ∨ (p3 → p1))) ∧ p2) ∨ p4)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320005247958294620026814474370 : (p4 ∨ ((p3 → (True ∨ p2)) ∧ ((p1 ∨ p1) ∨ (p5 ∨ (((p4 → ((p3 ∧ p5) ∨ ((p5 → True) ∨ ((True ∧ True) ∨ p3)))) ∨ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950291431337936178967788786040 : (((((p2 → True) → False) ∧ ((p1 → (p4 → (p2 → (p2 ∧ p1)))) ∨ (p3 ∧ (False ∧ (((p1 ∧ (p4 → p2)) ∨ p1) → (p4 ∨ True)))))) → p2) ∧ True) := by
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
    have h5 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118160982856192754798408463876 : ((False ∨ (((p4 → p1) → False) ∨ (p1 → (((p2 ∨ (p5 ∧ ((p5 → p2) ∨ (p1 → p5)))) ∨ True) ∨ (p4 ∧ (p3 ∨ False)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706942237689541600577595634401 : (((((((p2 ∧ p2) ∨ False) ∧ (p3 ∧ p3)) ∨ False) ∨ (True ∨ ((p3 → False) ∨ ((p3 ∧ ((p5 ∨ (p1 ∨ (p4 → True))) ∧ False)) ∨ False)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_61284893936452242942031681661 : ((False ∧ (p4 ∨ (p1 → ((p2 → p1) ∧ ((((p4 ∧ (p1 → (((p3 → (p1 ∨ p5)) ∧ True) ∨ p3))) → p4) → False) ∧ (p5 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109480930989490946463591774695 : ((p2 ∨ ((True → False) → (p2 → (False ∧ (p1 ∨ (p2 ∧ (p3 ∧ ((p3 ∧ (True → (True → (False → (p4 ∨ p3))))) → p2)))))))) ∧ (False → p3)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622456862012514705560669865076 : ((((p3 ∧ ((p4 ∨ p2) → ((False ∨ (((((True ∧ False) ∨ (p2 ∧ p3)) → (p1 → ((True ∧ True) ∨ False))) ∧ True) ∧ p4)) ∧ p1))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_726078322465500112019364771423 : (((((p1 ∧ True) ∨ p3) ∨ (p1 ∨ ((((((False ∧ ((p1 ∨ False) ∨ p3)) → False) ∨ p1) → True) ∨ (((p1 → p3) ∨ True) ∨ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41730146532049458468095282998 : (((((p3 ∧ p5) ∨ (False ∨ p4)) ∧ ((((((False → (p4 ∧ (True ∧ False))) ∨ p3) ∨ True) ∧ p4) ∨ (p1 → p3)) ∧ (False → p2))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349968671133771985315356793679 : (p4 → (((p2 ∨ (p2 ∨ ((p4 ∧ (True → (((p1 ∨ False) ∧ p5) ∧ (p3 ∨ ((p4 ∨ p1) → ((p1 → p5) ∧ p3)))))) ∨ p2))) ∧ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306218459875560850708496873494 : (p1 ∨ (((False ∧ p5) ∨ p5) → ((p1 ∧ ((p3 ∨ False) ∧ p3)) → ((((False ∧ (p4 ∧ (True → p4))) ∧ False) ∨ (p3 ∧ p4)) ∨ (p1 ∨ p5))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64795810811575662887064603656 : ((p2 ∨ (((p2 ∧ False) ∧ (((False ∧ p2) ∧ ((p3 ∧ p1) ∨ (((True ∨ True) → (p1 → (p4 ∧ True))) ∧ (True ∧ False)))) ∨ True)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46811216770795134372026293100 : ((((((((True → p4) → True) ∨ p4) → ((p4 ∨ False) ∧ ((True → (False ∧ ((p4 ∧ True) ∧ False))) ∧ p4))) ∨ True) ∧ p2) ∨ (p3 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113907417396098032832290959946 : ((((((((p1 ∧ p3) → p5) → ((p5 → (p3 ∧ (p3 ∧ p5))) → p2)) ∨ False) ∧ False) ∧ (p4 → p2)) ∧ (p3 ∨ (p1 → True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351400880239699472361427782331 : (p4 → ((((p5 ∨ (p4 ∨ p5)) ∧ (False → (p4 ∨ ((p5 ∧ p1) ∨ ((p5 ∨ True) ∨ p4))))) → (p3 ∨ p2)) ∨ ((p4 ∧ p4) ∧ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789246853854073456032381251530 : (((p5 ∨ ((((True ∨ p5) → p5) ∨ ((True ∧ (p2 ∧ (p3 ∨ p4))) → ((p3 ∧ (p5 ∧ p4)) ∧ False))) ∨ ((p5 ∧ p4) → (False ∨ p5)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310495534673529284625096518032 : (p2 ∨ (((p5 → ((p1 ∧ True) ∧ p3)) → p2) ∨ (True ∨ (((((p4 → True) → p1) → (p5 → (((p4 ∨ p3) ∧ p1) ∧ p4))) ∨ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711544810498623402850682056035 : ((((False → ((p4 → p1) → (False ∧ p5))) ∧ (((((p2 ∨ p1) ∨ ((p1 ∧ p3) → (p2 ∨ True))) → p2) → ((p1 → p2) → p5)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



