variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337078110743718444922168166785 : (p1 → ((((p2 ∧ ((((p5 ∧ p1) ∨ p3) ∧ (False ∧ (p3 → False))) ∧ (p5 ∨ (p5 ∧ p5)))) ∧ p1) ∨ (True ∧ (p2 → p2))) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303165144471254243406833088783 : (False ∨ (p4 → ((((((False ∧ (p5 ∨ p5)) → (False ∧ p3)) ∧ (True ∨ ((p4 ∨ True) ∨ p1))) ∧ ((p5 ∧ p2) ∨ p5)) → (p4 ∧ p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265620666931785316677869239297 : (True ∧ (p1 ∨ (p5 ∨ ((p4 ∨ ((p1 ∨ (p2 ∨ p3)) → p1)) ∨ (p5 → (((((False → False) ∨ p1) ∧ (p4 ∨ True)) → p5) ∨ (p5 ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51244955265701600078691398082 : (((((p2 → True) ∨ p4) → (((p1 ∧ ((p4 ∨ True) ∨ (True ∨ p4))) ∨ (p2 → p2)) ∧ p4)) ∨ (((p3 ∧ (True ∨ p5)) → True) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241267117260734552979760759277 : ((False → True) ∧ ((((p4 ∧ (((p2 → p1) → (((((False ∧ p2) → (p3 ∧ False)) → p3) → (p4 ∨ p4)) ∧ False)) → p3)) → p5) ∨ True) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179639001045064043755712342992 : ((p4 → (p3 ∨ (((p4 → (False ∧ p2)) ∧ p5) ∨ ((p2 ∧ p4) → p5)))) ∨ ((p2 → p2) ∧ ((p3 ∧ False) ∨ ((True ∨ p1) ∨ (p1 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188693366907779927335070345065 : (((p3 → ((p5 ∨ p3) → (p3 → p3))) ∨ (p2 ∧ False)) ∧ (((p4 ∧ ((((True → (p4 ∨ p5)) ∨ p2) ∨ False) → False)) ∨ (p3 → p3)) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154118208776769885339117902749 : ((((((False ∧ p3) ∧ ((p5 ∨ False) ∧ p3)) ∧ ((False → (p5 ∨ False)) ∨ (False → p5))) ∧ p3) ∨ True) ∧ (p5 → (((False → p3) ∨ p1) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248735266782799521855451181215 : ((p3 ∨ p2) ∨ (p4 → (False ∨ ((((p4 → ((False ∨ (True → p2)) ∨ p4)) ∨ ((True ∧ (p1 ∨ p1)) → p2)) → (p3 ∧ p5)) ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_216024757438380701660267163368 : ((p5 ∨ ((p5 ∧ p2) ∨ p2)) ∨ (((p5 ∧ p1) ∨ (False ∨ (((p1 ∨ (p5 → True)) → p1) ∨ ((p2 → p2) ∧ ((p5 → p4) ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47507177933669994257837718265 : (((p2 ∨ ((p2 → (True ∧ ((p4 ∨ (((p2 ∨ p4) → True) ∧ (False ∨ (p1 ∧ (p4 ∨ (p5 ∧ p1)))))) ∧ False))) ∨ p5)) ∨ (True ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200944760773014350458436139764 : ((p2 ∨ (((p2 ∧ (True ∧ False)) → p4) ∧ p4)) → ((p5 ∧ ((p3 ∨ ((p3 → p1) → (p2 ∨ True))) ∧ ((p1 ∧ (p2 ∨ p1)) ∨ p1))) → p1)) := by
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
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h36 =>
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- One of the premise coincides with the conclusion.
          exact h35
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115259489673274119005355952740 : ((((p5 ∧ p4) ∧ (False → (((p2 ∧ p4) → p5) ∨ True))) ∨ (((p2 ∧ p3) ∧ p2) ∨ (True ∨ ((p4 → (p2 → p1)) ∨ p3)))) ∨ (p2 → p2)) := by
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
theorem thm_5_vars_300546577966933437404239999346 : (False ∨ (((p3 → (True → (((((False ∨ p5) ∨ p5) ∨ ((p4 → True) → p3)) → p5) → p2))) ∨ (p1 ∧ p1)) ∨ (p5 → ((p1 → True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148664076278064546760811071367 : (((p5 ∨ (True → (((True ∨ p2) ∨ False) ∨ p2))) ∧ (((p4 ∨ True) ∧ True) ∧ (False ∨ (p1 ∨ (p5 ∨ p3))))) ∨ (p4 ∨ (p3 ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_116429149470159104917143593382 : (((True → (p5 ∨ p1)) → ((p4 ∨ (p2 ∧ (((p2 ∧ (p1 ∧ p3)) ∧ p1) ∧ False))) ∧ (p4 ∨ ((p2 → p2) ∧ (False → p5))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670406197240087196545450773168 : ((((((p4 ∧ p4) → p5) → ((((p1 ∨ (True ∨ p5)) ∨ ((p5 ∨ (p2 → (p4 ∧ p4))) → p4)) → False) → p2)) ∨ (p3 → (p5 ∨ p2))) ∨ False) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ (True ∨ p5)) ∨ ((p5 ∨ (p2 → (p4 ∧ p4))) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299299219212195668208906143076 : (False ∨ (((p3 ∨ ((p2 → ((True → p3) ∧ (True ∨ p2))) ∧ True)) ∨ (p2 ∨ (True → (p5 ∨ (((p4 ∧ p5) → p5) → (p3 → True)))))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234514283716036144672229737241 : ((p2 → (p2 → False)) → ((p5 ∨ (p1 → (p4 ∧ ((False → (p3 → True)) ∧ (p2 ∧ p5))))) → ((p2 ∨ ((p2 ∨ (p1 ∨ True)) → p2)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h7 := h1 h6
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h16 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ (p1 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h24 : (p2 ∨ (p1 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h25 := h15 h24
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309389618663353955270538255314 : (p2 ∨ ((p4 ∧ (p3 ∧ ((((p4 ∨ ((p4 → p5) → p2)) → (((p1 → p4) ∧ (p3 ∧ (p3 ∨ p1))) ∨ False)) → p3) ∧ p5))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592321881850224455906564420175 : ((((((((False ∨ (p4 ∧ ((p2 ∧ p1) → False))) ∨ (((False → p4) → p5) → (p2 ∨ p1))) → p2) ∨ (p5 ∧ False)) → (p3 ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46077327497389088681759993833 : ((((((p2 → ((p4 ∧ p4) → (True → (False ∨ p2)))) → (((False ∧ True) ∨ (p1 → p3)) ∧ p5)) → (p4 ∨ p5)) ∨ p5) ∧ (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797694485410176332043182984951 : (((p1 → ((p1 ∧ ((p3 ∨ (True ∨ p3)) ∧ (((True → p1) → (((False ∨ p2) ∨ False) ∨ (True ∧ True))) ∨ (True ∨ (p3 ∧ p5))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741402056676432406887118985883 : ((((p5 ∨ False) ∨ (p1 ∧ ((p4 ∧ p3) ∨ (p2 ∨ (p1 ∨ ((True → p2) → (((False → p2) → p5) ∧ (p2 ∨ ((p1 → False) → p2))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39411325167170131546056283934 : (((p4 ∧ ((False ∧ (p2 → ((p1 ∧ (p2 ∧ True)) ∨ (p1 → False)))) ∧ ((((p3 → (p2 ∨ p2)) ∧ p4) ∧ (False ∨ p3)) → p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177660913226592440497335619343 : ((((p2 ∧ (((p4 → (True → (p2 → True))) → p1) ∨ p2)) ∨ False) ∧ False) ∨ ((p1 ∧ p1) ∨ (False → (False ∧ (((p3 → False) → p4) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83150840365285104059710046767 : (((p5 ∨ (((False ∨ p5) ∧ (p4 ∧ (p3 ∨ p3))) ∨ (((p5 → False) ∧ p2) → ((False ∨ False) ∨ p2)))) → (p5 ∧ (True ∨ (p4 ∨ p2)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((False ∨ p5) ∧ (p4 ∧ (p3 ∨ p3))) ∨ (((p5 → False) ∧ p2) → ((False ∨ False) ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316890320641415814272396025974 : (p3 ∨ (p1 → (p1 ∧ ((((p2 → (True ∧ ((p4 ∨ True) ∧ p3))) → p1) → ((p1 → (p5 ∧ (p2 ∧ p1))) ∧ True)) ∨ (p2 → (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313147187292082732403089070852 : (p3 ∨ (((False → (((p3 ∨ (((p4 ∨ p5) ∨ p3) → p4)) ∧ p3) ∨ (p2 ∨ True))) ∧ (((True ∧ ((p2 ∧ p4) ∧ p3)) ∧ True) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301271389432317386412977900323 : (False ∨ ((p2 → ((p5 → p3) → (p3 ∨ False))) ∨ (p4 ∨ (p2 → (p5 → ((p4 ∧ (p4 → ((((False ∨ p5) ∧ False) → True) ∧ p5))) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112148825502036224858478178454 : (((p1 ∧ (False ∨ ((p5 → (True ∧ True)) → (((((p2 → p2) ∨ p3) → p5) ∧ p5) ∨ (p3 ∧ (p3 ∧ (p2 ∧ False))))))) ∨ True) ∨ (p1 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140423134555773365316641997299 : (((((False ∧ False) ∧ (False ∨ (p1 ∨ ((((p4 ∨ True) ∧ p4) ∧ p2) ∨ p1)))) ∧ (False ∨ True)) → ((p2 ∨ p3) ∨ p2)) → ((p2 → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349048616042497623805208437003 : (p3 → (p5 ∨ (((((p3 ∨ p5) ∨ ((p2 → (p1 ∧ True)) ∨ p2)) → ((p3 ∧ (p5 ∧ p1)) ∨ p1)) ∧ True) ∨ (p5 → (p4 ∨ (True ∨ p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179195883928236016091323251104 : ((p3 ∧ (False ∧ ((((p1 ∨ (p4 → True)) ∧ p1) ∨ True) → (p3 ∧ p1)))) ∨ (((p5 ∨ p2) ∧ False) → ((p2 → (p1 ∨ p4)) ∨ (p5 ∨ p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627914019764508613102984605560 : ((((((p5 ∧ ((p3 ∧ ((p5 ∧ (p2 → p2)) ∧ p3)) ∨ True)) ∨ (True ∨ (p4 ∧ ((True ∨ (p5 ∧ False)) ∧ (True ∧ p1))))) ∧ True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740322217049953965670661268018 : ((((p1 ∨ p1) ∨ ((((p4 ∨ p5) → False) ∧ (((p3 ∧ (p4 → (p2 ∧ ((p4 ∨ p1) ∨ True)))) ∧ (p1 ∧ p1)) ∨ p3)) ∨ (True ∨ p1))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184437669311073309657581354961 : ((((p2 ∧ p4) ∨ ((p5 → False) ∧ (p2 → p2))) ∧ (p5 ∧ p1)) ∨ ((((True ∨ (p5 ∨ False)) → ((False → p3) ∧ (False ∨ False))) ∧ False) → p3)) := by
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
theorem thm_5_vars_326136211652551083754812584946 : (p5 ∨ (p1 → (p1 ∧ (((p2 ∧ ((True ∧ (False → ((p5 → (((p5 ∧ p4) ∧ p4) → p1)) ∨ True))) ∧ False)) ∧ ((p4 ∨ p2) ∧ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721637892214100565744360955824 : ((((True ∨ ((p4 ∨ p2) ∧ p4)) → (((((p5 ∧ (p2 → True)) ∧ (p2 ∧ p2)) → (True ∨ (p2 ∧ True))) ∧ (False ∧ False)) ∨ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49825833697079248626832402318 : (((p3 → ((((True → p4) → (False → p5)) ∨ (p2 ∨ (p4 ∧ True))) ∧ (p5 → ((p1 ∧ p4) ∧ (p4 ∨ p1))))) → (p4 ∧ (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1297520982285146678380582670 : ((True → (((((p5 ∧ ((p2 ∨ (True ∨ p5)) ∨ (((p5 ∧ (True → p1)) ∨ p4) ∧ True))) ∧ p5) ∨ (p3 ∨ p2)) ∧ p1) ∧ p2)) → p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185499011126911417470555955431 : ((p2 ∨ ((p2 → ((p1 ∧ False) ∧ p3)) ∧ ((p2 → p3) ∧ False))) ∨ (((p3 → (p5 → (p2 ∧ True))) ∨ (((True ∨ p5) → False) → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994498983079634929097695683525 : (((p5 ∧ ((p3 ∨ (((p3 ∧ (p1 ∨ ((False ∧ p3) ∧ p1))) ∨ p4) ∨ (True ∨ ((False → p2) ∨ ((p2 → (True ∨ p1)) → p3))))) → False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (((p3 ∧ (p1 ∨ ((False ∧ p3) ∧ p1))) ∨ p4) ∨ (True ∨ ((False → p2) ∨ ((p2 → (True ∨ p1)) → p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44973380547387125210519650046 : ((((False → p4) ∧ (p3 → (p4 → ((((p3 ∨ ((p4 → True) ∨ ((p3 → p2) ∨ (p1 → True)))) ∧ p1) → p2) → (p5 ∨ p3))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198278060573141832160471546141 : ((False ∧ (p2 ∧ (((p3 ∨ p4) ∧ False) ∧ p3))) ∨ ((p1 → ((False ∨ p4) ∧ ((False → (p5 ∧ p3)) ∨ p4))) ∨ (p4 → (False → (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225321033407672795732493637414 : (((False ∨ p5) ∧ p1) ∨ ((False ∨ ((p3 ∧ ((p2 → True) → p2)) → (((p4 ∧ ((False → False) ∧ ((p4 ∧ p3) ∨ False))) ∨ p2) ∨ p5))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69192067632385155088495242039 : ((p5 → ((((True → ((p4 ∨ (p2 → (False ∨ p2))) ∨ p2)) ∨ p1) ∨ p2) → ((False ∧ p3) ∨ ((p3 → ((p4 → True) ∧ p5)) → p5)))) ∨ p3) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305048220633548011716697412203 : (p1 ∨ ((((p2 ∨ ((p3 ∧ p5) ∧ ((True ∧ (False → ((p3 ∧ p3) ∨ (p4 ∧ True)))) ∨ (p5 ∧ p2)))) ∨ p1) ∨ p4) → ((p1 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681754630295800530290682784147 : ((((((False ∨ ((((p3 ∧ p3) → ((p5 ∧ p1) ∧ False)) → p2) → (p3 ∧ False))) ∨ p4) ∧ p1) ∧ (True ∧ ((True ∧ (p2 ∧ p1)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192634717602029261888633076735 : ((((((p3 ∨ (p4 → p1)) → True) → True) ∨ True) → False) → (p2 ∨ ((p1 ∧ p4) ∧ (True ∧ (p1 ∧ (False ∨ ((False ∧ (p5 → p4)) ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ (p4 → p1)) → True) → True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118391774609965336577017713058 : ((p2 ∨ ((True → (p3 ∧ (p1 ∧ p4))) ∧ (p5 ∧ (((((p2 ∨ p4) ∧ (p4 ∧ p3)) ∧ p4) ∧ (False → p5)) ∨ (False ∨ False))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135147606731841514206434706919 : (((p5 ∨ (p3 ∨ (p5 → ((p5 → (p5 ∧ ((p4 ∨ (False ∨ False)) ∧ (p3 ∧ (False ∧ p5))))) ∧ p1)))) ∨ (p3 → p3)) ∨ (True ∨ (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68770117715623300428747875895 : ((p4 → ((((False → p1) → (p2 ∧ ((True ∨ True) ∨ p1))) ∨ p2) ∧ (p1 ∧ ((p3 ∧ (p5 → p4)) ∧ (p3 → ((True → p4) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248624462465050231959236210380 : ((p3 ∨ p1) ∨ ((True ∧ ((p2 → ((p5 ∨ p4) ∧ p5)) → (p2 ∧ ((p2 ∨ (((p2 ∨ True) ∧ p1) → (p2 → p4))) ∧ (p4 → p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351261573651610697359454765369 : (p4 → ((p2 ∨ (((((((p4 → (p4 → (p2 → (p2 ∨ False)))) → (p5 ∨ True)) → p5) ∨ p1) ∨ True) ∧ p2) ∧ p4)) ∨ (p1 ∨ (p4 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47447317749523219131560106608 : (((p3 ∧ (p1 ∧ ((p3 ∧ False) ∧ ((p1 → ((False ∧ ((p4 → p5) ∧ ((p1 → p2) ∧ (p3 ∧ False)))) ∨ False)) → p2)))) ∨ (True ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173224123650885526271913559358 : ((p5 ∨ (p5 → (((p2 ∨ ((p2 → True) → p1)) ∨ (False ∨ (p4 → p5))) ∧ True))) ∨ ((p5 → p1) ∧ ((((p2 → p4) → p1) ∨ p1) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137257540045291964839573186533 : ((p1 ∧ ((p5 ∧ p1) ∨ ((((p2 ∨ (p2 → ((p4 ∨ p4) ∧ ((p4 ∨ p1) ∧ p2)))) → (False ∨ p1)) ∨ p2) ∨ True))) ∨ (False → (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58078026702741730923683510527 : (((False ∧ p5) ∧ (p1 ∨ ((((p4 ∧ p5) → ((((p1 ∨ p1) ∨ p4) → (p3 ∨ p2)) → (p2 ∧ (p2 → p2)))) ∨ (True ∧ False)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115399509971190849303958665005 : (((p5 ∧ ((p5 ∧ (p2 ∨ (True → p2))) ∧ False)) ∧ ((p3 → True) ∧ (p5 ∧ (((((p4 ∧ True) ∧ p1) ∧ p3) ∧ p4) ∨ p1)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56065742335068782207244969812 : (((((p4 → True) → True) → p1) ∨ (((p3 ∨ p4) ∨ ((p5 ∨ ((p1 → False) ∧ p4)) ∨ (p4 → (p2 → p5)))) → (p4 ∨ (p2 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232292855132736507527986082265 : (((p3 → True) → False) → (((False ∨ ((p1 ∨ (((p4 ∨ True) ∧ (p3 ∨ (p5 ∧ True))) → p1)) ∨ (p1 ∧ ((p4 → p5) ∨ False)))) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624354846804872448650043871555 : ((((p3 ∨ (((p1 → p4) ∧ p4) ∧ (((p4 → (p1 ∨ False)) ∨ ((((p5 → False) ∧ p3) ∨ (False ∧ (True ∨ p2))) ∧ p4)) ∨ p2))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_115715690895576946986729203692 : ((((p3 ∧ (False ∨ (p1 → p4))) ∨ p2) → ((False → ((True ∨ p4) → (p1 ∧ (False ∨ ((True → p4) ∨ p1))))) → (p3 ∨ p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385633120422183065548765671484 : ((((((((True ∧ ((p4 ∧ (p2 → p1)) ∨ False)) ∨ False) ∨ p1) ∨ (((p2 ∧ (p3 → False)) ∨ p2) → (p1 → p4))) ∧ (p1 ∧ p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_49303413922941382090991435093 : (((False ∨ (p5 ∨ (p3 ∨ (p3 ∨ ((((False → p1) ∨ (p1 ∨ (((p4 ∨ True) ∧ False) ∨ False))) ∧ p2) ∧ p5))))) ∨ (p5 ∨ (p5 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151618320548781617876790819717 : (((False ∨ (p5 ∧ ((p1 → p4) → (False ∨ ((p4 ∨ (True → (True → (True ∨ p5)))) ∧ p3))))) → (True → p5)) → (False ∨ ((p3 → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3231636794984907950651010987 : ((p2 ∨ p1) ∨ (p3 ∨ ((((p1 → False) ∨ p1) ∨ p1) ∨ ((True ∧ (p5 ∨ ((p5 ∧ (p5 ∨ p1)) → (p5 ∧ (True ∧ p1))))) ∨ True)))) := by
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
theorem thm_5_vars_255803390378913306023574324739 : ((True ∨ False) → ((((p3 ∧ p4) → (False ∧ (False ∨ ((((((p1 ∨ p2) ∨ False) ∨ False) ∧ p1) ∨ p2) ∨ p2)))) ∧ p3) ∨ (p5 → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65811914008618599188745250402 : ((p4 ∨ ((p3 ∨ (p2 ∧ ((p5 ∨ (p4 ∧ False)) ∧ p2))) → (p2 ∨ (((p1 ∨ p5) → (((p2 → p4) ∧ p4) ∨ True)) ∨ (p3 ∧ p5))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192810594127543115575385039300 : (((False → (p4 ∧ (p4 ∨ (p3 → (False → p4))))) → False) → (((False ∨ (p4 ∧ False)) ∧ ((p1 → (p5 ∨ (False → p4))) ∧ (p3 → p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p4 ∧ (p4 ∨ (p3 → (False → p4))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25335328220901081070740240874 : ((((False ∧ p1) → p3) → ((((p3 ∨ True) ∧ (p4 → (p4 ∨ p2))) → p5) → ((p5 ∨ (p1 ∨ (((p1 ∨ p3) → p2) ∨ p4))) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ True) ∧ (p4 → (p4 ∨ p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185600192857781667655248056487 : ((p5 ∨ (p1 ∨ (((((True → p3) → p1) ∧ p4) ∧ p4) ∨ True))) ∨ (((p5 ∧ (p2 → ((p2 ∧ p2) ∨ False))) → ((False → p1) ∧ p2)) → p2)) := by
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
theorem thm_5_vars_686328040531434470957972594557 : ((((((p2 → (False ∨ (p4 → p2))) ∨ p2) ∨ ((p1 → p4) ∧ ((p1 ∧ (p1 ∨ p1)) ∨ p1))) → (True ∧ (p2 → (p3 ∨ (p5 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43521553697961129764758659483 : ((((p5 ∨ ((p1 ∧ True) ∨ ((p3 ∨ (((p1 ∧ p1) ∧ ((False ∨ False) ∨ p2)) → ((p5 ∧ (p2 ∧ p3)) ∨ p3))) → p2))) ∨ False) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184985770829132096558334933014 : (((True ∧ False) ∧ ((p2 ∧ p2) ∧ (p5 → (p4 → (p4 ∧ False))))) ∨ ((p1 ∨ True) ∨ (p4 ∨ ((p4 ∧ (False → (p3 → (p4 → p2)))) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208006153200226087228642614129 : ((((False ∧ p4) → p2) ∨ (p5 ∧ p5)) → ((True ∧ (((p3 → ((p5 ∧ (False → False)) ∨ p2)) → (p5 ∨ (True ∧ p2))) ∧ p1)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80248295514896460162937483500 : (((((p1 ∨ ((((p1 ∧ p3) ∧ p4) ∨ (p4 → (((p3 → p2) ∧ p1) ∧ p3))) ∨ p1)) ∨ (p5 ∧ p2)) ∨ (False → p1)) → (p5 ∧ False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((((p1 ∧ p3) ∧ p4) ∨ (p4 → (((p3 → p2) ∧ p1) ∧ p3))) ∨ p1)) ∨ (p5 ∧ p2)) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61272798467352485047434657614 : ((False ∧ (p2 ∨ (p4 ∧ ((False ∨ (p5 → (((False → (p4 ∨ (p5 ∧ p1))) → p1) ∨ ((p4 ∧ p4) ∧ (p1 ∨ p1))))) ∨ (p5 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313005530082429286220601443366 : (p3 ∨ ((((p5 → (((p3 ∧ p2) ∨ (p1 ∨ p5)) ∨ ((((p5 → (p1 ∨ True)) ∧ False) ∨ True) ∨ p4))) → ((p2 ∧ p5) ∨ p2)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206954526873387045938323648450 : (((((p3 ∨ p3) → p3) → p3) ∧ p1) → (((p2 ∨ (False ∨ (p3 ∨ p3))) ∨ ((p4 ∨ False) ∨ True)) ∨ ((p3 → p4) → (p4 ∧ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596265270399687181342988798671 : (((((False ∨ ((((p2 → p4) ∨ p4) → p1) ∨ p1)) ∧ (False ∧ ((True ∧ (p3 → p5)) → ((p5 ∨ ((False ∨ p3) ∧ p2)) ∧ False)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113500889434362778184465136561 : (((((p1 ∨ p4) → ((p2 ∧ p4) → (p5 ∧ (p1 → ((p2 ∧ p2) ∨ (p4 ∨ True)))))) → (p2 ∨ (p3 ∨ p3))) ∨ (True ∧ True)) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67901172432935132748786424081 : ((p2 → ((((p1 ∨ ((((p4 ∨ p3) → p3) ∧ p1) ∧ (p1 → False))) ∧ p3) ∨ p4) ∧ ((p4 ∨ p1) → ((False ∧ p3) ∧ (p3 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199922017780978507715730419099 : ((((False ∧ p1) ∨ (True → p2)) ∨ (p3 ∧ False)) → ((p1 → ((False ∧ (((False → p2) ∨ ((p4 ∧ p2) ∨ False)) → (False ∧ p3))) ∧ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147873008982443542072057569348 : (((p3 → (p4 → (((p5 ∨ True) ∧ (p1 ∨ p3)) → ((p2 → ((p5 ∨ p3) ∨ p2)) ∨ (False ∧ p5))))) → p4) ∨ (True ∨ (p2 ∧ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114342134741349971103514580668 : (((p2 ∨ ((((((p1 ∨ p4) ∨ (p1 ∧ True)) → p5) → (p3 ∨ p4)) ∨ True) ∨ (False ∧ True))) ∧ ((p1 → (p3 ∧ p3)) ∨ True)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354921694685491540149894470482 : (p5 → ((p2 ∨ ((((p2 ∧ (((p1 → p2) → (True → p5)) ∧ p4)) ∨ (p3 ∧ True)) ∧ ((p5 ∧ ((p4 ∧ p1) ∨ p1)) ∨ True)) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259024862379000382578269183059 : ((True → p4) → (((p1 ∨ p1) → ((((p3 → ((p3 ∨ ((p4 ∨ p2) ∧ p2)) ∨ p2)) ∨ p2) ∧ p2) ∧ p3)) ∨ (True ∨ ((p2 → p2) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208727970768360023329324025090 : ((p1 ∧ ((True ∨ True) ∧ (True → p4))) → ((((p1 → True) → p2) ∧ ((p4 ∧ ((True ∧ p5) ∨ p3)) ∨ False)) ∨ (((p4 ∨ p4) ∨ p2) ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- One of the premise coincides with the conclusion.
    exact h13
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351442150382104281634732969127 : (p4 → ((((p3 ∨ (((p1 → p4) → p5) ∧ p4)) ∨ (p4 ∧ ((True ∧ (False ∨ False)) ∨ (p3 ∨ p1)))) → p2) → ((p4 ∧ p2) ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698728504313163177105670716634 : (((((p4 → p2) ∧ (p4 → (((p5 → (p1 ∧ p5)) ∨ p2) → p3))) ∨ (((p5 ∨ (((p4 ∨ False) ∧ (p2 ∧ False)) → p5)) ∧ False) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_40625544942357199406659194727 : ((((((((p5 ∨ False) → (p5 ∨ p3)) ∨ (p4 ∨ (p2 ∧ ((True → ((p1 ∨ (p1 ∧ False)) ∧ p4)) ∧ p4)))) ∧ p2) → p4) → p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65197587556650499368426843149 : ((p3 ∨ (((((True → (p2 ∨ p3)) ∨ p2) ∧ ((False ∨ False) ∨ (False ∧ (((p1 → (p1 ∧ p3)) → p4) ∨ (p4 ∨ True))))) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171828093632744189504275688549 : (((((True → True) ∧ p1) ∧ (p5 → ((((p2 ∨ True) → p1) → p4) ∧ p3))) → p3) ∨ ((((((p5 ∨ p4) → True) ∨ p1) ∨ p4) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348170241152750512561740757642 : (p3 → ((p1 ∨ p3) → ((((p2 ∨ p4) ∧ (((p1 → p2) ∧ (p4 ∧ ((True ∨ (p3 → p2)) → p2))) ∨ True)) ∨ p1) ∨ ((p2 ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58506137483402961617604508015 : (((p4 ∨ p4) ∧ (p4 → ((p5 ∨ (((p1 ∨ ((((p3 ∧ p4) → p5) → True) → True)) → True) → (((p4 ∨ p3) ∨ p5) → p5))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317147169341028320077586641522 : (p3 ∨ (p5 → (p4 → (True ∧ ((p4 → ((True → ((p4 ∧ (True ∧ (p1 ∧ p4))) ∨ (True ∨ (p4 ∨ (False ∧ (False ∧ p2)))))) → p2)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47752387281405732027618382566 : (((((p3 ∨ (p3 → p2)) → ((p3 ∧ p5) → (((p2 ∨ (p2 → False)) ∨ ((p5 → p5) ∧ False)) → (p3 ∧ p3)))) ∨ p4) → (p1 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218785804701834809729998199710 : ((p1 ∧ ((p2 → p1) → p4)) → (((((False ∨ p3) ∨ (p3 ∨ (True ∨ ((False → p5) → p2)))) → (p5 ∨ (p5 → (p1 ∨ p4)))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



