variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50282809802333091574859857281 : (((((p3 → (p5 ∧ ((p3 → ((p4 → p3) → (p2 ∧ (p2 ∧ True)))) → False))) → True) → (p1 → p3)) ∨ (((p5 → p2) ∨ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355042381138613903224896278959 : (p5 → ((((((p3 ∧ (p1 ∨ p1)) → (False → p5)) → False) ∧ (((p5 ∧ p4) → (p3 → p4)) ∧ (p2 → (p3 ∧ (p5 → False))))) ∨ False) → p1)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 ∧ (p1 ∨ p1)) → (False → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h8
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315231748210715178412791921969 : (p3 ∨ (((p4 ∨ (False ∨ p5)) ∧ p3) ∨ (((True ∧ ((False ∨ ((((False ∧ p2) → p5) ∧ p1) ∧ True)) → (p3 ∨ True))) ∨ (p4 ∨ p1)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112508491756395310652365436922 : ((((((p1 → p3) → ((((True ∧ p4) ∨ p5) ∧ True) → (((((p1 ∨ True) → p1) → p1) ∨ True) ∨ p2))) ∧ p5) → p2) → p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123862931948056300816980121113 : ((((p4 ∧ (False ∨ (True ∧ (p1 ∧ p4)))) ∨ (True ∨ ((p3 → p5) → True))) → (((True ∨ (p3 ∨ p1)) → p3) ∧ (False ∧ p5))) → (p2 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (False ∨ (True ∧ (p1 ∧ p4)))) ∨ (True ∨ ((p3 → p5) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234789513806767408354393819900 : ((p5 → (p2 ∧ False)) → (((p3 → ((p4 → ((((False ∨ ((((p5 ∧ True) ∧ True) ∨ False) ∧ p5)) ∧ p1) ∨ p1) → False)) ∧ p1)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721812083428828611836659795452 : ((((p3 ∨ ((p3 ∨ p5) ∧ True)) → (((((p3 ∨ False) ∧ (p3 ∧ p2)) ∨ (p2 ∨ True)) ∨ (True ∧ ((p4 → p4) → p4))) ∨ (p3 ∨ p3))) ∨ p4) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173181045173227017571028578449 : ((p4 ∨ (((p2 ∨ p4) ∧ p4) ∧ (False → (((p3 ∧ p5) ∧ (p3 ∧ p4)) ∨ p3)))) ∨ (((p1 → (p5 ∨ (p1 ∧ (p4 → True)))) ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693948204825459497437242471536 : (((((((p1 ∧ p1) ∨ (((True → p1) → p3) ∧ False)) ∧ False) ∨ (False ∨ p4)) ∨ (p5 ∧ (((p1 ∧ False) ∧ p4) → ((True ∧ p5) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659304559905692364285274136008 : ((((p5 → ((((p4 ∨ p1) ∧ (((p1 → p4) ∨ (p4 ∨ p2)) ∧ (True → p3))) ∨ False) → (p3 ∧ ((True ∧ False) ∨ p5)))) ∨ (False ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h15 := h8 h14
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h18 := h8 h17
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h5.left
      let h21 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h24 := h21 h23
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h28 := h21 h27
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h31 := h21 h30
          -- One of the premise coincides with the conclusion.
          exact h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h35.left
      let h45 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h46 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h49 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h50 =>
    -- False on the left can always be used.
    apply False.elim h50
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173335733430664276812472945795 : ((p2 → (True ∧ (((True → (p3 ∧ p4)) → (False ∨ p1)) ∨ ((p1 ∧ p5) ∧ p1)))) ∨ ((p2 ∧ (p4 ∨ (p1 ∧ p1))) ∨ (p4 ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145253519803840270175043259611 : (((p4 ∨ (p1 ∨ ((p2 ∨ False) ∧ (p4 → p3)))) → ((p3 ∧ (False ∧ ((p1 ∧ (True ∨ p2)) ∧ p4))) ∨ True)) ∧ (((p2 ∨ p3) ∨ True) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147433103953511908768985892275 : ((((p2 ∨ (p4 ∧ p1)) → ((((p2 ∨ p1) ∨ ((p2 → True) ∧ True)) ∨ p1) → (False ∨ (p4 ∨ True)))) ∨ p4) ∨ (p4 ∧ ((p1 ∨ p3) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164997272329570910590070545178 : ((((p2 → (((False ∧ (p5 → p4)) → p5) → p1)) ∧ (True ∨ (p3 ∨ (p4 → p2)))) → p3) ∨ (((p4 ∨ p2) ∧ (False → p2)) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353675020133225898809828655497 : (p4 → (p5 ∨ ((((((p5 ∧ False) → p2) → False) → ((p5 → p3) ∧ (False ∨ p5))) → False) ∨ (((False → (p2 ∨ (p2 ∧ p1))) ∧ p4) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109986719095713666689014638904 : ((True → (p5 → (((p4 ∨ p2) ∨ p4) ∨ (True ∧ (((p2 ∨ (((p2 → p5) ∧ True) ∨ p1)) ∨ (p2 → False)) ∨ (p5 → p4)))))) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136122747715080744682397986444 : (((p4 ∨ ((p1 ∨ p2) ∨ ((False ∨ p4) → p5))) ∨ (p4 → (((((False ∧ p4) ∨ (p1 → p3)) ∧ p5) ∨ True) → p2))) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40717361663378942404756066614 : ((((((p5 → p2) ∨ ((p5 ∧ p3) → (p1 → p5))) ∨ (False → (((p5 → (((p3 → p1) ∨ True) ∨ p1)) ∨ p4) ∨ p5))) → p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61790944259397801444763503534 : ((p2 ∧ ((p5 ∨ (p5 ∨ ((True ∨ ((p1 → ((False ∧ (p1 ∨ p5)) → ((((p3 ∨ p3) ∧ p2) ∧ p3) ∨ False))) ∧ p5)) ∧ p2))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184437069241757840661018317378 : ((((p5 → True) ∧ ((True ∧ (p3 ∧ p2)) ∨ p4)) ∧ (p4 ∨ p4)) ∨ ((p2 ∧ (p4 → p1)) → ((True ∨ p4) → ((False → (p3 ∧ p2)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56219260568958023528540953344 : (((p2 ∨ (False ∧ (False ∨ p1))) ∨ (((((p1 → p2) ∧ p3) ∧ p5) ∨ (((p5 ∧ p3) ∨ p1) → True)) ∨ ((p5 ∧ False) ∧ (p4 → p3)))) ∨ p2) := by
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
theorem thm_5_vars_110732912262430263483174044898 : (((((True ∨ (False ∧ (((p3 ∧ p5) ∧ True) ∧ (p4 → p1)))) ∧ (((p2 → (False ∧ p3)) ∧ p1) ∨ (p2 ∧ p4))) ∧ p2) ∧ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58330152352842504216524465464 : (((False ∨ p1) ∧ ((p1 ∨ p1) ∨ ((True ∧ (True ∧ (False ∧ (p4 ∧ p3)))) ∨ (((p1 ∨ p5) → p3) ∧ ((p3 → (True ∧ p4)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172022426415599775096946116938 : ((((False ∨ (False → True)) → (False ∨ ((p3 → (p1 ∧ p5)) ∨ False))) ∨ (p3 → p5)) ∨ (True ∧ ((True ∧ (p2 → False)) ∨ ((p5 ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_248577159808924676910810697315 : ((p3 ∨ False) ∨ ((p1 ∧ ((((p4 ∨ (p5 → ((p5 ∨ p4) ∨ (True → (p3 ∨ p1))))) → p3) ∨ (False ∨ False)) ∧ p5)) ∨ ((False → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207409086971292296754976522887 : (((p4 ∧ (p3 → (p4 → p5))) ∨ False) → ((p2 ∨ (((((True → True) ∧ (p3 → True)) ∨ ((p2 ∨ False) ∨ True)) → p3) → (p2 → False))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148437818848375613755667194012 : (((p2 ∨ (((p1 ∨ ((True ∨ p4) ∨ (p5 → (p3 ∨ p1)))) ∧ p5) → p1)) → ((p5 → p1) ∧ (p4 ∨ p5))) ∨ (p3 ∨ ((True → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152818695137821461677804940163 : (((p3 ∨ True) → (((p2 ∧ p2) ∨ (((False ∨ ((p3 ∨ p3) ∨ p2)) ∨ p1) ∧ (p2 ∧ (p3 ∧ p4)))) ∧ False)) → ((p1 ∧ True) → (True → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49146894073230844388590442986 : ((((True → ((p3 → (p1 → (p2 ∨ (False → p4)))) ∧ p1)) → ((p4 ∧ False) ∨ ((False ∧ p1) ∧ (True ∧ p3)))) ∨ (p2 ∨ (False → True))) ∨ p5) := by
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
theorem thm_5_vars_780055392969009708607255388658 : (((p2 ∨ ((True → (p4 ∧ (((((False ∧ ((p1 ∨ (p5 ∧ True)) ∧ p3)) ∧ ((p3 → p4) ∨ p1)) ∧ p1) ∨ p1) ∨ p1))) ∨ (False → p4))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_180584928891478391134429865453 : (((p2 ∧ ((p5 ∨ p2) → (p2 → (p4 ∨ p1)))) → (p5 ∧ (p1 ∧ p2))) → (p4 → (((p1 → p4) → False) → ((p5 ∧ (p5 ∧ p1)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53655503897494076398295048147 : ((((p1 ∧ p1) ∧ ((p5 → (False ∨ p3)) ∧ (p4 ∨ False))) ∧ (p1 ∧ (True → (p3 → (p4 → (((p4 → p3) ∧ (p4 → True)) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670901224987197995578435719988 : ((((p3 ∧ ((False ∧ p5) ∧ (((((((True ∧ (p1 ∨ (p2 ∧ False))) ∧ True) → False) ∨ False) → p5) ∧ p5) ∧ p4))) ∨ (True → (p4 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248202177667340097331261471465 : ((p2 ∨ p1) ∨ ((((p1 → ((False ∨ ((False ∨ p5) → p2)) ∧ (False → (p1 ∧ False)))) ∨ (False ∨ (False → (True → (p4 → p3))))) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → ((False ∨ ((False ∨ p5) → p2)) ∧ (False → (p1 ∧ False)))) ∨ (False ∨ (False → (True → (p4 → p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112239505739914413917344856156 : (((p3 ∨ (((True → False) ∧ (p2 → ((((p1 → (p3 ∨ p3)) ∧ p5) → False) ∨ ((p4 ∧ p1) ∧ (True ∨ p5))))) ∧ p2)) ∨ True) ∨ (p5 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192308374845419862290388493312 : (((p1 ∧ ((p3 ∨ (p5 ∧ p1)) → (p5 ∨ p5))) ∧ p2) → (((False → (True → ((p3 ∨ False) → (p4 → (True ∨ (p3 → p2)))))) → p3) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134126068300887075254267959600 : ((((p5 ∧ ((p4 ∨ (((p3 ∧ (True → ((p3 ∧ True) ∨ p2))) → (p4 ∧ True)) → p1)) → p3)) ∨ (p4 → p1)) ∨ p1) ∨ ((p3 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892482560818292239629850512216 : ((((((p2 → p5) ∨ (p5 → ((True ∧ (((False ∧ (p3 ∨ p1)) ∨ p4) ∧ (p1 → (p3 ∧ p3)))) ∨ p3))) → False) ∧ (p3 ∧ (p5 → p3))) → p1) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → p5) ∨ (p5 → ((True ∧ (((False ∧ (p3 ∨ p1)) ∨ p4) ∧ (p1 → (p3 ∧ p3)))) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158403660193471329653668886725 : (((True ∧ p1) ∨ ((p2 → True) → ((((p4 → p3) ∧ False) ∨ p3) ∧ ((True ∧ (p2 ∨ p4)) ∨ p3)))) ∨ (False → (True ∧ (p5 ∧ (p5 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59280410629165248102663544126 : (((p3 ∨ p2) ∨ ((p1 ∧ p2) ∨ (((((((p4 → False) ∧ True) → False) ∨ p1) → p1) → (p3 ∨ (p5 ∧ ((p5 ∨ False) ∨ p5)))) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199251049816533451422132166442 : (((p3 → (p4 ∧ ((p5 ∧ False) ∨ False))) ∧ p3) → (False ∧ (False ∧ (((False → ((p4 → (((p5 ∧ p5) ∨ p4) ∨ p2)) ∨ p5)) ∧ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h22 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h23 := h20 h22
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124204327858797714734882155347 : (((p4 ∨ (((p3 ∨ True) ∧ ((p2 → p4) ∧ True)) ∨ p5)) ∨ ((((True ∧ (p5 → False)) ∧ p5) ∨ (False ∧ p1)) ∧ (False → p2))) → (False ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h7.left
          let h10 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h7.left
          let h13 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193174091322333022537349549899 : (((((p4 ∨ p2) ∨ p1) ∨ True) → (p1 ∧ (p4 ∧ p1))) → ((((p4 ∨ p4) ∨ False) ∨ ((False ∨ (((p3 ∨ p5) ∧ p1) ∧ p4)) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245839752718166067697425789579 : ((p3 ∧ p4) ∨ (((p2 ∨ (p2 ∨ ((True ∧ (((((p2 ∨ p5) → p4) ∨ (p3 ∨ (False → p5))) ∨ p4) → p3)) → False))) ∧ p4) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657022562861146432161408064378 : ((((((p5 → False) ∧ p5) ∧ ((p1 → p4) ∨ ((True → (p3 → ((False ∨ (p2 → p5)) → p4))) ∧ ((p3 ∧ p5) ∧ p3)))) ∨ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50348893637650454101119807387 : (((((p3 ∨ (p2 ∨ p3)) → p3) ∧ (p2 → (True ∧ (((p1 ∨ (p2 → p1)) ∨ (p3 ∨ p1)) → False)))) ∨ (((p1 ∨ True) → False) → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135900282722163144214625490208 : (((((((p1 → (p4 ∧ True)) ∨ (False → p1)) → p3) ∨ p5) → p3) → (True ∧ ((p4 ∧ (p4 ∨ (True → True))) ∨ p1))) ∨ (False → (p5 ∧ p5))) := by
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
theorem thm_5_vars_748558769177572566065545203266 : ((((p3 → False) → ((((p1 ∨ p3) ∨ p5) ∧ p5) ∨ (p1 ∨ ((p4 ∧ (p3 ∨ (p2 ∨ True))) ∨ (((p1 ∧ p1) ∨ (False ∨ True)) ∨ p3))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_135741205405450748230773916827 : ((((p3 ∧ (p1 ∧ (((p4 ∧ p3) → p3) ∧ True))) ∨ ((p2 ∨ p4) → p3)) ∨ ((p2 ∧ ((p4 ∨ True) ∨ p5)) ∧ p1)) ∨ (True ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808557465771215918690515664039 : (((p4 → (p5 ∨ (p2 ∨ ((p3 → ((((p5 → True) → p5) → p5) ∧ p1)) → ((p1 ∧ p4) ∨ (((p4 → (True ∨ p1)) ∧ True) ∨ p5)))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217578744704006989719558347880 : ((((p1 ∨ p5) ∨ p2) → False) → (((p2 ∧ (p4 ∨ p3)) → (False ∧ ((p2 → False) ∧ False))) ∨ (p1 → ((((p4 ∨ p5) ∨ p5) ∧ p1) → p2)))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : ((p1 ∨ p5) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((p1 ∨ p5) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : ((p1 ∨ p5) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229883163054868289930137373933 : ((p5 → (p4 ∨ p3)) ∨ ((p2 ∨ (p3 ∧ ((((p2 → (False ∧ p5)) → (True ∨ ((p4 ∨ False) ∨ p3))) ∧ p4) ∨ p3))) ∨ ((False ∧ True) → p5))) := by
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
theorem thm_5_vars_172343222381601703753358667777 : (((p1 ∨ (((p4 ∧ True) ∧ p5) ∨ p4)) ∧ ((p3 ∨ ((p2 → p3) → p1)) ∨ p1)) ∨ ((((p2 → p5) → (False ∧ (p3 → p4))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180735354977648921313518810725 : (((((True → p3) ∨ p2) ∨ p1) ∨ (((p4 ∨ p3) ∨ (p1 ∨ p5)) ∨ p3)) → (False ∨ ((p1 ∧ ((((p3 ∧ p5) → p3) ∨ True) ∧ False)) → p2))) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h9
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h17
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- False on the left can always be used.
        apply False.elim h25
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h25
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h37 =>
            -- False on the left can always be used.
            apply False.elim h36
          case inr h38 =>
            -- False on the left can always be used.
            apply False.elim h36
        case inr h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h45 =>
            -- False on the left can always be used.
            apply False.elim h44
          case inr h46 =>
            -- False on the left can always be used.
            apply False.elim h44
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h49
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h54 =>
            -- False on the left can always be used.
            apply False.elim h53
          case inr h55 =>
            -- False on the left can always be used.
            apply False.elim h53
        case inr h56 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h57
          -- Conjunctions on the left can always be decomposed.
          let h58 := h57.left
          let h59 := h57.right
          -- Conjunctions on the left can always be decomposed.
          let h60 := h59.left
          let h61 := h59.right
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h62 =>
            -- False on the left can always be used.
            apply False.elim h61
          case inr h63 =>
            -- False on the left can always be used.
            apply False.elim h61
    case inr h64 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h65
      -- Conjunctions on the left can always be decomposed.
      let h66 := h65.left
      let h67 := h65.right
      -- Conjunctions on the left can always be decomposed.
      let h68 := h67.left
      let h69 := h67.right
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h70 =>
        -- False on the left can always be used.
        apply False.elim h69
      case inr h71 =>
        -- False on the left can always be used.
        apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165407351345516303440361565844 : (((((p4 ∨ (((p3 ∨ (True ∧ p2)) ∨ p1) ∧ p4)) ∧ False) ∨ p5) → ((p5 → True) → False)) ∨ (((((p4 ∨ p4) ∨ p3) ∨ True) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p4) ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343579564434644265563130388744 : (p2 → ((False → p1) → ((p3 ∧ p5) ∨ (((((((p3 ∧ False) ∧ (p3 ∧ False)) ∨ p3) ∧ False) ∨ (p3 ∧ (False → (p4 ∧ False)))) ∨ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218387051016804211889170411593 : (((p5 → p3) ∨ (p3 ∨ False)) → ((True ∨ p5) ∧ (((p5 ∨ (p1 ∨ ((p2 ∧ p5) ∧ p4))) ∧ ((p3 → True) → (p2 ∧ False))) → (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h17 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h19 := h8 h17
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h23 : (p3 → True) := by
            -- Implications on the right can always be decomposed.
            intro h24
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h25 := h8 h23
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h36 =>
          -- False on the left can always be used.
          apply False.elim h36
  -- Conjunctions on the left can always be decomposed.
  let h37 := h6.left
  let h38 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h40 =>
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h41 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h42
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h43 := h38 h41
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h47 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h48
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h49 := h38 h47
        -- We need to get the right conjuct of h49 based on <expert-advice>.
        let h50 := h49.right
        -- False on the left can always be used.
        apply False.elim h50
      case inr h51 =>
        -- False on the left can always be used.
        apply False.elim h51
  case inr h52 =>
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h54 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h55 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h56
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h57 := h38 h55
        -- We need to get the right conjuct of h57 based on <expert-advice>.
        let h58 := h57.right
        -- False on the left can always be used.
        apply False.elim h58
      case inr h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
          have h61 : (p3 → True) := by
            -- Implications on the right can always be decomposed.
            intro h62
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h38, we can now drive its conclusion.
          let h63 := h38 h61
          -- We need to get the right conjuct of h63 based on <expert-advice>.
          let h64 := h63.right
          -- False on the left can always be used.
          apply False.elim h64
        case inr h65 =>
          -- False on the left can always be used.
          apply False.elim h65
    case inr h66 =>
      -- Conjunctions on the left can always be decomposed.
      let h67 := h66.left
      let h68 := h66.right
      -- Conjunctions on the left can always be decomposed.
      let h69 := h67.left
      let h70 := h67.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h71 =>
        -- One of the premise coincides with the conclusion.
        exact h68
      case inr h72 =>
        -- Disjunctions on the left can always be decomposed.
        cases h72
        case inl h73 =>
          -- One of the premise coincides with the conclusion.
          exact h68
        case inr h74 =>
          -- False on the left can always be used.
          apply False.elim h74



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799136861186172138574431785382 : (((p1 → (False ∧ ((p3 ∧ ((p1 → (p2 ∨ p3)) ∧ (p3 → ((p3 ∨ (True → (p3 ∨ ((False ∧ p1) ∧ p2)))) → p2)))) ∨ (p2 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740838460767571966724179264898 : ((((p3 ∨ False) ∨ (((((((False → (p5 ∧ p1)) → (False ∧ p5)) ∨ p1) → False) → p1) ∧ True) ∧ ((True → p1) ∨ ((p1 ∨ p5) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303892150095580217093828945963 : (p1 ∨ ((((((False ∨ p3) ∨ (p4 ∧ (p4 → ((p2 → p3) ∧ p5)))) → p5) ∨ (p2 ∨ p5)) ∨ (p4 ∨ (True → ((False ∨ p3) ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337678379310945853777780549004 : (p1 → ((p3 ∨ ((p4 → (p4 ∧ ((p3 → False) ∨ False))) → ((p3 ∨ ((p2 ∨ p1) ∧ p3)) ∧ p3))) ∨ ((p4 → False) ∨ ((p2 → True) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206102577240253405467821327459 : ((p4 ∧ (((p5 ∧ p3) ∨ p3) ∧ p2)) ∨ ((p1 ∧ (p4 ∨ ((True ∨ False) ∧ p3))) ∨ (p2 → (True → ((True ∧ (False → False)) ∨ (p1 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646355111588175851376173048061 : ((((False → (p1 ∨ (((False → ((((p4 → p3) ∨ (True ∨ (p4 ∨ p2))) → p1) ∧ True)) → ((p3 → p4) ∨ True)) ∧ (p1 → p3)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117219940487180775536887707637 : ((True ∧ ((p5 ∧ p1) ∧ (p1 ∧ ((True ∧ p5) ∨ ((True ∧ p3) ∨ (p1 ∧ (((p1 → p1) → (p1 ∧ (p1 ∧ p5))) ∧ p3))))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51277183276648035895515432945 : (((False ∧ (p5 ∨ (True ∧ ((((p2 ∨ False) ∨ True) ∧ (False ∨ p1)) ∧ ((False ∨ p4) ∧ p1))))) ∨ ((p3 ∧ (p3 ∧ p3)) ∧ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52531815515911281912389816901 : (((((p1 ∨ (p4 ∧ p5)) ∧ (((p5 → False) ∨ p1) ∧ (p5 ∨ True))) ∨ p1) ∨ ((p1 ∨ (p4 ∨ p3)) → ((p3 → (p2 ∧ True)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315468879558944766112550898099 : (p3 ∨ (((p2 ∨ False) ∨ p3) → ((p5 ∧ (((False → ((p2 ∨ (p2 ∧ p2)) ∧ (False ∧ (True ∧ p1)))) ∧ p1) ∨ p4)) → (True → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136419495551589246930132514968 : (((((p2 → p4) ∨ p5) ∨ p5) → ((((p3 → (p5 → ((p3 ∧ (p5 → False)) ∧ p1))) ∨ False) ∨ (p4 → p4)) ∨ p2)) ∨ (p3 ∧ (False → p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58854228271932209047751203454 : (((True ∧ p3) ∨ (p3 ∨ (p1 → ((True → p2) ∨ (((False ∧ True) ∨ (p4 ∨ ((p1 → p5) ∨ (False ∧ (p1 ∨ p1))))) ∧ (False → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218225864239217233896522421618 : (((p5 ∧ True) ∨ (p2 ∧ p1)) → ((False ∧ (((p5 ∧ p5) ∧ (p3 ∧ p3)) ∧ p2)) ∨ ((p2 → False) ∨ ((False → p4) ∨ ((p5 → p1) → p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723447677629611179668791300667 : (((((p3 ∧ p4) → p3) ∧ (((p2 ∨ (((p1 ∨ p3) → p2) ∧ (((p4 ∧ p1) ∨ p4) → p5))) → p4) ∧ (p5 → ((p1 ∨ p4) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185591936122977575834319179286 : ((p5 ∨ ((p3 ∨ (p5 ∧ p4)) ∨ (p4 ∧ ((False ∧ p2) ∨ p3)))) ∨ ((False ∧ (((p3 ∧ p5) ∧ p4) ∧ False)) → (((p2 ∧ p4) ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228859025975810689724445898962 : ((p3 ∨ (p4 → p2)) ∨ ((p3 ∨ (p4 ∨ (p2 ∨ (((p3 ∨ p3) ∧ p4) ∨ (True ∧ True))))) ∨ (True ∧ ((p5 ∧ ((p1 ∨ False) ∧ False)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699599238867266422577788800254 : ((((((((p4 → p1) ∨ p3) ∨ (False → (False ∧ p4))) → p3) → True) → ((((p5 ∧ (p3 → ((p1 ∨ False) → p1))) ∧ p2) → p3) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_43587967930678654455267278207 : ((((((p4 ∨ ((p2 ∨ False) ∧ (True ∧ p2))) ∧ (p3 ∧ ((p3 ∨ True) ∨ (True ∧ ((p3 ∨ (True → p2)) ∨ p5))))) ∨ p2) → p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341072698725004260387766168814 : (p2 → ((p5 ∨ ((p4 → False) → (p4 ∧ (p3 ∧ (((p1 → (((False ∨ p2) ∧ p3) ∧ p2)) ∧ (p3 → p5)) → ((p3 ∨ p1) ∧ True)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654158616480939752350795931038 : ((((((((p5 ∨ (((p1 → p5) → (p2 ∨ ((p4 ∨ False) ∨ (True ∧ (p3 ∨ True))))) ∧ False)) ∨ False) ∨ True) ∨ p2) ∨ p5) ∨ (p2 ∧ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118399053884470281664064847944 : ((p2 ∨ ((p1 ∧ (p4 ∧ p4)) → (p3 ∨ (((p1 ∧ (False → True)) → p2) ∨ (((False ∨ (p2 → p5)) → (p3 ∧ p3)) ∧ False))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254291131670801068666815031803 : ((p2 ∧ p3) → ((p4 ∧ ((False → p2) ∧ (((False ∨ (p5 ∧ (p3 → p5))) → p4) ∧ p4))) ∨ (p3 ∧ ((p1 ∨ p1) ∨ (p1 → (p2 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134305615789827619140880970822 : (((True ∧ ((((((p1 ∧ True) ∧ (p2 ∧ p2)) ∧ False) ∨ (p3 ∧ (True → ((False ∧ p2) ∧ p3)))) ∨ False) ∨ True)) ∨ p4) ∨ (True ∨ (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688097410707127746380432114647 : (((((((p1 ∨ p4) ∨ p1) → p3) → (((p2 ∨ p2) ∧ p5) ∧ (True ∨ (p1 ∨ p3)))) ∧ ((p4 ∧ (p1 → ((p2 ∧ p4) ∨ True))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893098283421245255399744309513 : (((((p2 ∨ ((((p1 ∨ (True ∨ p3)) → p3) ∧ False) → ((p4 ∨ False) ∧ p4))) → (True ∧ (p2 ∧ (p3 ∨ False)))) ∧ ((p2 ∨ p1) → p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ ((((p1 ∨ (True ∨ p3)) → p3) ∧ False) → ((p4 ∨ False) ∧ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h13 : (p2 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h13
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159384216878643428631934005630 : ((((True ∨ (((p3 ∨ p5) → (p4 ∧ (((p3 ∧ True) ∨ (False ∨ p5)) → p5))) ∧ p2)) ∨ p5) ∧ p3) → ((p2 ∨ (p2 → False)) ∨ (p2 ∨ p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58320402699176998799977884235 : (((False ∨ True) ∧ (p1 → (p4 ∨ ((p4 ∧ ((p4 → p3) → p3)) ∨ ((p5 ∧ p3) ∧ (((True ∧ (False ∧ (p2 ∨ p1))) ∧ p1) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315044768071373119864399647395 : (p3 ∨ ((((p4 ∨ True) ∨ (p3 ∧ (p2 → p3))) → False) → ((((p3 ∧ (False ∧ (False ∨ (p5 ∧ False)))) ∧ (False ∧ False)) ∨ p4) ∧ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ True) ∨ (p3 ∧ (p2 → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141475007958000250373666186640 : (((True ∨ (p1 → p4)) ∧ (p1 ∧ (((True → ((p5 ∧ (p1 ∧ p2)) ∨ (p2 ∧ ((p3 ∨ p1) → False)))) ∨ p5) ∨ False))) → ((p2 ∨ False) ∨ True)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
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
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679525177843867544113510468414 : (((((((True → p4) ∧ (((((p1 ∨ p1) → p3) ∧ p3) → False) ∧ p2)) → (True → (p1 ∧ p3))) ∧ p5) → (p1 → (p2 ∨ (p1 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323202431890452448078401891997 : (p5 ∨ ((((False → (p4 ∨ ((p1 → (False → False)) → p2))) → (((True → (p4 ∧ p5)) ∨ p3) ∧ (p2 → p1))) ∨ (p4 ∨ False)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44292732801880960644045438850 : ((((((p1 ∧ p1) → ((p4 ∨ p5) ∨ p5)) → ((False ∧ p1) ∨ (p4 ∧ (p1 ∨ True)))) ∧ ((p4 ∧ p2) ∧ ((True ∨ p4) ∧ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749314946425687290876140443789 : ((((p5 → p5) → (p3 ∧ (p4 ∨ ((p2 ∨ (True ∧ (((p1 ∨ ((True ∧ False) ∧ p3)) → ((p1 → p3) ∨ p2)) ∧ p4))) → (p2 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52995644124632769634536945223 : ((((p4 → ((p5 ∧ p5) ∨ ((False ∨ False) ∧ p4))) ∨ (True ∨ p2)) ∧ ((True → ((p2 ∧ p3) ∧ (p1 ∨ (p1 ∧ p4)))) ∨ (False → p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120592998595618173236736471431 : ((((p2 ∨ ((p2 ∧ (True ∧ ((((p5 → p4) → p2) → ((True ∧ False) → p5)) → p3))) ∨ ((p4 → p3) → p4))) ∨ True) ∨ p1) → (p5 ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54094953436486583423061710822 : ((((False → False) → ((p5 → (p5 → True)) ∧ (False ∧ True))) → (False ∨ ((((p3 ∧ True) ∨ ((p2 ∨ p4) ∨ (p4 → True))) ∧ p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137799560438156207362806462456 : ((p2 ∨ (p3 ∨ (((((p3 → False) ∨ False) → (((p3 ∨ (p3 ∧ p2)) → (p5 ∧ p5)) → (False ∧ p4))) ∨ True) → p4))) ∨ (p2 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323983930616382899238982936670 : (p5 ∨ ((((False → p3) → ((p1 → ((p1 ∨ (p2 → p1)) → True)) ∧ p5)) ∨ p2) ∨ ((p1 → ((p3 → False) ∧ (False ∨ p2))) → (p3 → p3)))) := by
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
theorem thm_5_vars_40997547924184137126457062373 : ((((p1 → (((p3 → False) ∨ (p1 ∧ ((p5 ∧ ((p2 ∨ (p3 → p4)) → p2)) ∧ (True ∧ (p2 → p1))))) ∨ p1)) ∨ (p1 ∧ p2)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138859014723032450023065802398 : (((p1 ∨ ((((p2 ∨ ((True ∧ (p2 ∧ ((p1 → (p2 ∧ p4)) ∧ p2))) → (p2 ∧ False))) → p4) → p5) → False)) ∧ p2) → ((p5 ∧ p5) → p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (((p2 ∨ ((True ∧ (p2 ∧ ((p1 → (p2 ∧ p4)) ∧ p2))) → (p2 ∧ False))) → p4) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746256894252378666212229928579 : ((((p1 ∨ p5) → (((((p1 ∨ ((False ∨ p4) ∨ ((p3 ∧ (True ∧ p4)) ∧ (((p4 ∧ True) → p2) ∧ False)))) ∨ False) ∨ p2) ∧ p1) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_826783783072098299463500961427 : (((((p3 → True) → ((p3 ∨ p1) → ((((p2 ∨ ((p2 ∧ p2) ∧ (p5 ∧ (True ∨ p5)))) → p5) ∧ ((p2 → False) ∧ p2)) ∧ p4))) ∧ p1) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350238595309862211866078321756 : (p4 → (((False → False) → ((False ∨ (False ∨ ((False ∨ ((p1 → ((p5 → (p2 ∧ True)) ∨ False)) → (p3 ∧ False))) ∧ (p5 → p4)))) ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



