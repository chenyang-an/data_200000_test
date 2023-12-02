variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711744640017341713830440837717 : (((((((p2 ∨ p1) ∧ p3) ∨ p4) ∧ p3) ∨ (((((False → p4) → ((p3 → (False ∨ p4)) ∨ p3)) → p4) ∨ True) → ((True ∨ True) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255123282523415269426510581446 : ((p4 ∧ p3) → ((p2 ∨ (((p3 → ((p2 → (p5 ∨ p4)) ∨ True)) ∧ p2) ∨ ((((p1 → p4) → False) ∧ (p1 → (False → p4))) ∨ p4))) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337669527818455569434401903591 : (p1 → (((p4 ∧ False) ∧ (p2 ∨ (p1 → (True ∧ ((p2 ∨ ((True → p1) ∧ p2)) ∧ (p4 ∧ p4)))))) ∨ (p5 ∨ ((True ∧ (p2 ∧ p2)) → True)))) := by
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
theorem thm_5_vars_135751516484407927614080705636 : ((((p5 ∨ False) ∨ ((False ∧ p2) ∧ ((p3 → (p4 ∧ (p2 ∧ p3))) ∧ False))) ∨ ((False ∨ (False → (p3 → p1))) ∨ p3)) ∨ ((p4 → p1) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626921716560662677831252617230 : ((((p5 → (True → ((p4 → ((p5 ∨ (p5 → False)) ∧ (p1 ∧ p1))) → (((((p2 ∨ (True → p2)) → p3) → True) ∧ p4) ∧ p4)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203863277621709851322113888483 : ((False → (False → (p2 ∨ (p3 ∧ False)))) ∧ (((True ∧ ((True ∧ (p1 ∧ False)) → p4)) ∧ ((((p4 ∨ p2) ∨ p5) ∧ p1) ∧ (p5 ∧ False))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821428108775674591149069652681 : ((((((True → True) → (((True ∨ False) → (p2 ∨ (p5 ∨ (p5 ∨ p2)))) → False)) ∧ (((p4 → (p3 → p3)) ∨ p3) ∧ (p3 ∨ True))) ∧ p5) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h10
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((True ∨ False) → (p2 ∨ (p5 ∨ (p5 ∨ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h17 := h12 h13
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h19
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : ((True ∨ False) → (p2 ∨ (p5 ∨ (p5 ∨ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h22
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h28 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h29 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h31 := h4 h29
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h32 : ((True ∨ False) → (p2 ∨ (p5 ∨ (p5 ∨ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h33
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h35 =>
          -- False on the left can always be used.
          apply False.elim h35
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h36 := h31 h32
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h38 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h39
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h40 := h4 h38
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h41 : ((True ∨ False) → (p2 ∨ (p5 ∨ (p5 ∨ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h42
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h44 =>
          -- False on the left can always be used.
          apply False.elim h44
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h45 := h40 h41
      -- False on the left can always be used.
      apply False.elim h45
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591778434956915525599308899045 : ((((((((p5 ∧ ((p5 → True) ∧ ((True → (((p1 ∨ True) → p3) ∨ False)) ∧ p2))) ∧ False) ∧ p5) ∨ (True ∧ p3)) ∨ (p4 ∨ p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2824359169723509922930395167 : ((((p4 → p1) ∨ False) → p4) → ((((p2 → (((p5 ∨ p1) ∨ (p3 ∧ p3)) → p3)) ∧ False) ∨ (True ∨ (p2 ∨ p4))) ∨ (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51316355473279453301887429384 : (((p4 ∨ (p2 ∧ (False ∨ (((p1 ∧ ((p3 ∧ p2) ∧ ((False ∧ p4) → p5))) ∧ p1) → p4)))) ∨ (p5 ∨ (((p3 → True) → True) → True))) ∨ p5) := by
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
theorem thm_5_vars_147330401433689034573984023149 : (((((((p5 → ((p4 ∧ p5) ∨ (False ∨ p1))) ∧ (True ∨ (p2 → p2))) ∧ p2) ∧ p2) ∨ (False ∨ p5)) ∨ p1) ∨ ((True ∨ p3) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319934940169437737431327751206 : (p4 ∨ ((p3 ∨ (p4 ∧ (p1 ∨ True))) → (((p1 ∨ (p3 ∨ p3)) ∨ (p3 → True)) ∨ (False ∨ ((p3 ∧ ((p1 ∧ True) ∨ (True ∨ p4))) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233297455067339505219019572442 : ((True ∨ (p2 ∨ p4)) → ((p1 ∨ False) → ((False ∧ p2) ∨ (((p3 ∧ (p4 ∧ (p5 → ((p1 ∧ p2) → p3)))) ∧ p4) → ((p2 ∧ False) ∨ p1))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h29 =>
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664631069189972896573982709765 : ((((True → (((((False ∧ (True ∨ True)) → False) ∨ p5) ∨ (p2 ∨ p3)) ∧ (((p4 → p2) ∨ p5) → ((p2 → p3) ∨ True)))) → (False ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218616953510041169935000202718 : (((p5 → p2) → (p3 ∨ p3)) → ((p3 ∧ ((True → ((p2 ∨ p2) ∧ ((False ∧ (p2 ∧ (p2 ∧ p2))) ∧ p5))) ∨ False)) ∨ (False → (p1 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57915456377636144910950087516 : (((p5 ∨ (p5 ∧ p2)) → (p4 ∧ (p1 ∨ ((p1 ∨ (p3 ∧ False)) ∧ (((True ∧ p2) → (p3 ∧ True)) → (False → ((p4 ∧ p3) ∨ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319941402653997183441340725326 : (p4 ∨ ((p3 → (p1 → (p1 ∨ True))) → ((p1 → (p5 → ((((p1 ∨ (False → (p2 → p4))) ∧ p1) ∧ (p5 ∨ p1)) ∧ p4))) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_342293649015319708695156045334 : (p2 → (((p4 ∧ p2) ∨ ((p4 ∨ p5) → (((False → p5) → (p2 ∨ ((False → False) ∧ p4))) → False))) ∨ (False → ((p5 → (p4 ∧ p4)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115943121574703466005803522773 : (((p1 ∨ (p4 ∨ (p1 ∧ p3))) ∨ (((((p2 ∨ (p2 → (p1 → p5))) → (p1 ∨ True)) → (False ∧ (p4 → p1))) ∨ p1) ∧ p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198559497756912530695935363488 : ((p1 ∨ ((True → (p1 ∨ (p3 ∧ p1))) ∨ False)) ∨ (p3 ∨ ((p3 → True) ∨ (((p2 ∨ ((False → ((p2 ∨ p5) ∨ p2)) → p2)) ∧ p4) ∨ False)))) := by
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
theorem thm_5_vars_115619985988845608707325538258 : (((p2 → (((p5 ∨ p1) → p4) → p1)) ∧ ((p4 ∧ (((p4 ∧ p1) ∧ ((False ∨ p2) → p2)) ∧ p5)) → ((p2 ∨ False) ∧ p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56738461568640993821251530280 : ((((p5 ∨ p2) ∨ p5) ∧ ((p5 → ((p1 ∨ p1) ∨ (p1 ∧ ((((p2 → True) → ((p5 ∨ p1) ∧ (p3 → p4))) → p2) ∧ p4)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141119873478523978635529262628 : (((False ∨ ((p4 → p4) ∧ (p4 → (False → p2)))) → ((p1 → (p4 ∧ p3)) ∧ (((False ∧ (p1 ∧ p2)) → p1) ∧ False))) → ((p3 ∧ True) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161391901068229195305208287130 : ((p1 ∧ (((False → p2) ∨ (p5 ∨ (p3 → (p4 ∨ (p5 ∧ p5))))) ∧ ((p1 → (p4 → p4)) → p4))) → (p4 ∧ (False ∨ ((p5 ∨ p2) → p4)))) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : (p1 → (p4 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h13
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : (p1 → (p4 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h18
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : (p1 → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h30 := h25 h27
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h31
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h36 : (p1 → (p4 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h37
        -- Implications on the right can always be decomposed.
        intro h38
        -- One of the premise coincides with the conclusion.
        exact h38
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h39 := h25 h36
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h40
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h42 =>
        -- One of the premise coincides with the conclusion.
        exact h39
    case inr h43 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h44 : (p1 → (p4 → p4)) := by
        -- Implications on the right can always be decomposed.
        intro h45
        -- Implications on the right can always be decomposed.
        intro h46
        -- One of the premise coincides with the conclusion.
        exact h46
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h47 := h25 h44
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h48
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- One of the premise coincides with the conclusion.
        exact h47
      case inr h50 =>
        -- One of the premise coincides with the conclusion.
        exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69658195219992195759633288726 : ((((True → ((p5 ∨ ((((((False ∨ True) → ((p1 → False) ∨ (p4 ∧ p3))) → p5) ∧ p5) → p1) ∨ p5)) ∧ (p3 → False))) ∧ p3) ∧ p3) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112009267175267248469608459134 : (((((p1 → (True ∨ True)) → p4) → (((True ∧ p5) ∧ (((p4 ∧ (True → False)) ∧ (False → p4)) ∨ (True ∧ p5))) → p2)) ∨ True) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319306612514446197115414685886 : (p4 ∨ ((((p3 ∨ (((False ∨ p1) ∧ p3) ∨ True)) → (False ∨ False)) ∨ (p1 ∨ (p2 ∧ p1))) → ((p2 ∨ p3) ∨ (p3 → ((True → p5) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172212622793695454971022739463 : ((((p5 → p4) ∧ (p5 ∧ ((p3 ∧ (p2 ∧ False)) → True))) → (False ∧ (True → p1))) ∨ (((((True ∧ p2) ∧ p3) → (p2 ∨ p5)) ∨ p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149889957297500880025656887891 : ((p2 ∨ ((False ∨ p1) ∨ (p5 ∨ ((p1 → ((p5 ∨ False) ∨ p1)) ∨ (((p3 ∨ (p4 → p4)) ∧ p1) → p2))))) ∨ (((False → p3) ∨ True) ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597212206137549887098377450679 : ((((((True ∧ (p5 ∨ p4)) → False) ∧ (((p1 ∨ p4) → (((p3 → p4) ∨ ((p5 ∧ p3) → (p2 ∨ False))) → False)) → (p2 ∨ False))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247860530851788638278820244227 : ((p1 ∨ p2) ∨ (((False → (p3 → True)) ∧ False) ∨ (False ∨ (p4 ∨ (((p4 ∨ p4) ∧ (p3 → ((True → (p1 ∨ (p4 → p5))) → p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_589210933248710820154241691711 : (((((((((p5 ∧ (((p2 → p2) → ((False ∨ p3) ∧ p3)) ∨ (False ∧ p2))) ∨ p5) ∨ True) ∨ ((True ∨ True) → p4)) ∧ p3) → p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698834620364529162087910275758 : ((((True ∧ ((p5 ∨ (p4 ∨ (False ∨ p2))) ∧ (p2 → (p5 ∧ p3)))) ∨ (((((p5 ∧ p1) ∧ p2) ∧ p3) ∨ p3) ∧ ((p4 → True) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209087058059758845730465021159 : ((p2 ∨ ((p5 ∨ (p1 ∧ p4)) ∧ p2)) → (((p5 → ((p2 ∧ p3) ∨ ((p1 ∧ (p1 ∨ True)) ∨ (((p4 ∧ False) → p1) ∨ False)))) ∧ p2) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219621527707281949345824192297 : ((False → ((p5 ∨ p4) ∧ p2)) → (((((True ∧ p4) ∨ True) ∧ ((((True ∧ (p2 → True)) → ((True ∨ p5) ∧ p1)) ∧ p3) → p1)) ∨ p4) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ (p2 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597291306210364250860547228672 : (((((p4 ∧ ((p4 → p3) ∧ p1)) ∧ (((p3 ∨ p2) ∨ (p1 ∨ p4)) → (p2 ∧ (p2 ∨ ((False ∨ p3) ∧ ((p2 ∧ False) → p1)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315152540255333020011579179252 : (p3 ∨ ((((p3 ∧ (p1 ∧ p1)) ∨ True) → p3) → ((p3 ∧ ((p3 → ((((p1 → p3) ∧ p1) ∨ False) → True)) ∨ p3)) ∨ ((p5 → p1) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p1 ∧ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124291507091062562827844083669 : (((((((True ∨ False) ∧ False) ∧ p5) ∨ p2) → p1) ∧ ((p5 → p4) ∧ (False → ((p4 → (p4 ∧ ((p3 → p1) ∨ p4))) ∧ False)))) → (p4 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124413383332511757190832315763 : (((((True → p5) ∧ (False ∧ (p1 ∧ True))) ∧ p5) → ((True → False) → ((True → p3) ∨ (((p4 → (p2 ∨ p5)) → p4) ∧ p2)))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313200915681822126522723779991 : (p3 ∨ (((p4 → ((p4 ∨ p4) ∧ p3)) ∨ (p4 ∨ (((((True ∧ p3) ∧ p1) ∨ p5) → ((p4 ∨ False) ∨ p1)) ∨ ((p1 → True) ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115127429729622583558225340100 : ((((((p1 ∨ p4) → p5) ∧ p3) ∨ (((p5 ∨ p2) ∧ p2) ∨ p1)) → ((p4 ∨ (p2 ∨ ((p2 → p3) ∧ p3))) ∨ (p1 → False))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117721437651775977554255245931 : ((p3 ∧ (p5 ∨ ((p3 → (((((True → p4) → ((p4 ∨ p2) ∨ True)) ∧ p4) ∧ ((p3 ∨ p3) ∧ (p1 ∨ p3))) → p2)) ∨ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312241095418352561071222707310 : (p2 ∨ (p1 → ((False ∧ (((((False ∨ p3) → p2) ∧ (p1 → (p5 ∧ p4))) ∨ ((((False → p4) ∨ p2) → p5) ∧ p5)) ∧ p4)) ∨ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246724226483375716004853619101 : ((p5 ∧ p4) ∨ (p3 ∨ ((p3 ∧ (((False → p2) ∧ ((((p1 ∧ (p2 ∨ p2)) ∨ p5) ∨ p2) ∨ (p3 → False))) ∨ ((p2 ∧ p3) → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300802782372913804803144989817 : (False ∨ (((((True ∨ (False ∨ True)) ∨ False) ∧ ((p2 ∨ (p2 → p1)) → (p4 → p3))) ∧ p5) → (p1 → (p3 ∨ ((p3 ∧ (p5 ∧ p1)) → p5))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56189821496754198719305975513 : (((p4 ∧ (p4 ∨ (p4 → False))) ∨ (((False ∧ ((((p3 ∨ p5) ∨ True) ∨ p1) ∨ ((p2 ∧ p2) ∧ p2))) → (p3 → p2)) → (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60931322942228308805215119097 : ((False ∧ (((p5 → False) ∧ ((p4 ∧ p2) ∨ ((p1 ∨ (((True ∧ (p5 ∧ p1)) ∨ p5) ∧ (False → ((True ∨ p3) ∧ p4)))) → p1))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165603926306710250583077402502 : (((((p3 ∧ p2) ∨ p2) ∨ ((True → p3) ∨ p4)) → (False ∧ (((p1 ∨ False) ∨ p4) → True))) ∨ (True ∨ ((False ∨ (p4 → (False ∧ p1))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736074507272379901672772473986 : ((((True → p5) ∧ (((p2 → (p1 ∨ (False ∨ (p2 → (p2 → (p3 ∨ (p4 ∨ (p1 ∨ False)))))))) → p3) ∧ (p2 ∧ ((False ∨ p2) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157529331857218287386728392350 : (((((p5 → ((p1 → ((False ∧ False) → p1)) ∨ (p2 ∧ (p5 → p1)))) ∨ p2) ∧ p1) → (p3 ∧ p3)) ∨ ((False → (p3 → (p1 ∧ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354858575847449212034461302882 : (p5 → (((p1 ∨ p1) → ((p2 ∨ (p5 → ((p5 ∨ p4) ∧ (p5 ∧ ((p3 → ((p1 ∨ (p5 ∧ (True → p3))) → p3)) ∨ p4))))) → p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685026942921269141891536553547 : ((((p5 ∧ (p4 ∧ ((p3 ∧ (p3 ∨ (p5 ∧ ((True ∨ True) ∨ ((p4 → p2) ∨ p5))))) ∧ True))) ∨ (p2 ∨ ((p5 ∧ p1) ∨ (p5 ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314926018996022998920346795789 : (p3 ∨ (((p3 ∧ (p3 ∨ p1)) ∧ (p1 → ((True → True) ∧ p3))) ∨ ((p5 ∨ (((((False → True) ∧ p2) ∧ p2) ∧ False) → p1)) ∧ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306268776630446554186845114903 : (p1 ∨ ((p3 → (p5 ∨ True)) → (((p2 ∨ ((True → p1) → False)) ∧ (((p2 ∧ p2) ∨ p3) → ((p3 ∨ p2) ∧ p3))) ∨ (p5 → (True → True))))) := by
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
theorem thm_5_vars_263411278687632065815070438318 : (True ∧ (((True ∧ p4) ∨ (((((p3 ∨ p5) ∧ False) ∨ p1) ∨ ((p5 ∨ (p3 ∨ True)) ∧ ((p1 → p4) → False))) ∨ p1)) ∨ ((p2 ∧ False) → True))) := by
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
theorem thm_5_vars_146972924583377611570979362865 : (((((p2 ∨ ((p2 ∨ p4) → ((False ∨ ((p3 ∨ (p4 ∨ False)) ∨ p5)) → p5))) ∧ (p3 → p2)) → False) ∧ p3) ∨ (p3 → ((p5 ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179396812356386536842809707968 : ((p3 ∨ (((True ∨ p2) → p4) → (p2 ∨ (True ∧ ((p2 ∨ p5) → p1))))) ∨ (((p1 ∧ (((p3 ∨ False) ∨ p5) ∧ False)) ∧ True) → (p1 ∧ p5))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147305380192870770625460917885 : (((((False → (True ∨ (p4 → ((p5 ∨ True) → p5)))) ∨ ((p2 ∨ p5) ∨ (True ∨ (p4 ∨ p1)))) → p1) ∨ p4) ∨ (((p3 ∨ True) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347380520972767551829263195692 : (p3 → ((((p5 ∨ p2) → p1) ∨ ((p2 ∧ p1) ∨ p4)) ∨ (p5 ∨ (((((p1 → p4) ∨ True) → ((False ∨ p3) → (True ∧ p2))) ∨ True) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178462898809845219639700368606 : (((p4 ∨ (p1 → (p3 ∨ (True ∨ (p2 ∧ p3))))) ∧ (p4 ∨ (p4 ∧ p2))) ∨ (((p5 ∨ p5) ∨ ((False → ((False ∨ p2) ∨ p1)) ∧ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800176325363609949840939668682 : (((p2 → ((p3 → (((p2 → False) ∨ (((False ∨ ((False ∧ p4) ∧ ((True ∧ (p5 → True)) ∨ (True ∧ p3)))) ∧ p5) ∨ True)) ∨ p5)) ∧ True)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71102595317524586291953209714 : ((((((False → p2) → False) ∧ p5) ∧ (False → (p1 ∨ ((p1 → ((((p5 → (p3 ∨ p2)) ∧ (p5 ∧ True)) ∧ p1) → False)) → p2)))) ∧ True) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351468770005766083141088402160 : (p4 → ((True ∨ (((p2 ∨ ((((True ∨ (True ∧ (p3 ∧ p5))) ∧ (False ∨ p3)) → False) ∨ p1)) → False) ∧ p3)) → (p1 ∨ (False ∨ (p1 ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170988446899879903560539828980 : ((p2 ∨ (p4 ∨ ((((p2 ∨ (False → (p5 ∨ p3))) ∨ (False ∧ p2)) → p4) ∨ True))) ∧ (False → ((True → (True ∧ ((p5 ∧ p3) ∨ p5))) ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165621253452338572329796570710 : ((((((p1 → p2) ∧ p1) ∧ p5) ∨ p3) ∧ (((p2 → p4) ∧ p2) ∨ ((p2 → p1) ∧ p3))) ∨ ((p2 ∨ (p2 ∨ p1)) ∨ (True ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38081446679290671089093489458 : (((((p5 ∨ p4) → (((False → p5) → ((p3 → (p4 ∨ (p4 → p4))) ∨ (p4 ∧ ((p2 ∧ p2) ∧ p1)))) ∨ p4)) → (p5 ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151545647651834073969580153366 : (((((p2 ∨ (p4 ∨ (p4 ∨ True))) → (((True ∧ (p4 → p4)) ∧ (True ∨ p5)) ∧ True)) ∧ p4) → (True ∨ p4)) → ((True → p3) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_66631155677335058986291073766 : ((True → ((p4 ∧ (((True ∧ ((p4 → False) → False)) → (False ∨ p4)) ∧ (p5 ∨ True))) ∨ ((p4 ∨ (True ∨ p2)) ∨ ((p2 ∧ p3) ∧ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_114185517456429642665975493753 : (((((p3 ∨ p5) → (p2 → (False ∧ (((p5 → p3) ∨ (True ∨ p2)) → False)))) → (p3 → (p1 ∨ False))) → ((p4 ∧ p3) → p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253125793594095207073883919694 : ((True ∧ p5) → (((((p2 → (p1 ∧ ((p1 ∨ p2) ∧ ((p1 → (False → (p4 ∨ p5))) → p1)))) ∧ (p2 → p4)) → p1) ∨ p5) ∧ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586930227009527049294883332921 : (((((p1 ∨ (p4 → ((((((False ∨ True) → (p5 ∨ ((p2 → p1) ∧ p4))) → p5) → False) → p5) ∨ ((p4 ∧ p3) ∧ p2)))) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114464008880181969226705096109 : (((((False ∨ True) ∧ ((((p3 → p5) ∧ ((p5 ∨ False) ∧ p4)) ∨ (p2 ∧ p1)) ∧ p4)) ∨ True) → (False ∧ (p3 → (p3 ∨ False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185757317611292295564560679641 : ((p4 → (((p2 ∧ (p3 → True)) → (p1 ∧ (p1 → False))) ∧ p5)) ∨ (((((p2 ∧ (True → False)) ∨ False) → True) ∨ False) ∨ ((False → p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320478605737485237410497630049 : (p4 ∨ ((p2 → p5) → (((p5 ∨ (p2 ∧ (((True → (p2 ∨ False)) → p3) ∧ (p4 → p3)))) ∧ p3) ∨ ((((p3 ∧ p1) → p3) ∧ True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158421440449107877042114358286 : (((p4 ∧ p1) ∨ ((((p2 ∧ ((True ∧ False) ∨ p5)) ∧ ((True → True) ∨ (True ∧ False))) ∨ p2) → p1)) ∨ (p5 → (p5 → ((False ∨ True) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658482993085518274146049435285 : ((((p1 ∨ (p4 ∧ ((p3 ∨ (p4 ∨ ((p4 → (True → p1)) ∨ ((p4 ∨ ((p1 ∨ (p2 ∧ p3)) ∧ p1)) ∨ True)))) ∧ p1))) ∨ (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114081772358602684173164526480 : (((((p5 ∧ p4) ∨ p5) → (((p2 → ((p1 → ((p2 ∧ p1) ∧ (True → True))) ∨ p2)) → p2) ∨ p2)) ∨ ((p3 ∧ p1) ∧ p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312243126910596675549144736567 : (p2 ∨ (p1 → ((((False ∧ (((p3 → ((p5 ∨ p2) ∧ True)) → p3) ∧ (p2 ∨ p2))) ∨ ((p1 ∨ False) ∨ p4)) ∧ p1) ∧ ((False → p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355229140255094093519582482457 : (p5 → (((p5 → (p3 ∨ (p4 ∧ p2))) ∧ (((p1 ∧ (p3 ∨ (p5 ∧ p1))) → p1) → ((p1 ∧ (p5 ∧ ((p5 ∨ p4) → p2))) ∧ p4))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∧ (p3 ∨ (p5 ∧ p1))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h5
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150418740628524586961906096371 : ((((((p1 ∨ (p3 ∨ p4)) ∧ ((True ∨ p4) ∨ p4)) ∨ ((p4 ∨ p3) → ((True ∧ p1) → p3))) ∨ True) ∧ p5) → (p3 ∨ (p5 ∨ (p4 ∧ p3)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h14
            case inr h17 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h14
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h3
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225587868565191567543875356926 : (((False → p3) ∧ p4) ∨ (((False ∨ (((p1 ∧ p4) ∨ ((((False → p3) ∨ p5) ∧ False) ∨ True)) → p1)) → ((p4 → p1) ∧ True)) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244717993540599882014155521208 : ((p1 ∧ True) ∨ (False ∨ (((False → p1) ∧ ((((p1 → p1) ∨ True) ∨ p3) ∨ (p1 ∧ False))) → (False ∨ (((p2 → p1) → p1) → (p4 → p4)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317728269395928951286096806515 : (p4 ∨ ((((True → (True ∧ p3)) ∨ ((((p4 ∨ ((True ∧ p5) → (p3 ∧ p3))) ∧ False) ∧ p2) ∨ (False ∨ True))) ∧ (p4 → (True ∨ p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150026629129574816985089941420 : ((p5 ∨ ((p3 ∨ (p2 ∨ p4)) ∧ (True → (False ∧ ((p2 ∧ (p1 ∧ p3)) ∧ (p2 ∧ ((False ∧ p3) ∨ p5))))))) ∨ (((p1 ∨ p2) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782904011226110837470412827458 : (((p3 ∨ (((p1 ∨ (False → (True ∧ ((False ∨ p3) → (((p2 ∨ (True ∨ ((p2 → p1) ∧ True))) ∧ p5) ∧ p3))))) → p4) ∧ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305771534788752227021891848903 : (p1 ∨ (((p2 → (False → (p4 ∧ p4))) → (p3 ∨ p3)) ∨ ((((False → p5) ∨ ((((p4 ∧ p4) ∨ (p5 → p3)) ∧ True) → p2)) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216954791288822532546844439245 : (((p1 → (True → p3)) ∧ True) → (((True ∧ p1) ∨ (True ∨ (((True → p1) → (p4 ∧ p3)) → (p1 → (p4 → (p3 → False)))))) → (p4 ∨ True))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668365545697634725156347340636 : ((((p5 → (p4 ∧ (True ∧ (((((((p4 → (p2 ∨ p3)) ∧ (p1 → p5)) ∧ True) → p1) ∧ p2) ∧ p2) → False)))) ∧ ((p2 ∨ p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632719217600736791481403704334 : (((((p5 → ((False ∧ (p3 ∨ ((p4 ∧ (p4 ∧ True)) ∧ p2))) ∨ ((((p5 ∨ p2) ∨ p2) ∨ p5) ∧ ((p4 ∧ p1) ∨ p2)))) → p3) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117246602462018736001257678058 : ((True ∧ (p3 ∨ ((p1 ∨ (p3 → True)) ∧ (p3 → (p2 → ((p1 → p5) ∧ (((p2 ∨ p2) → False) ∧ ((False ∨ False) ∧ True)))))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779426210404094925946866406164 : (((p2 ∨ ((((p1 → p1) → ((((((False → False) → p3) ∨ True) → ((p1 ∨ (True ∨ p1)) ∨ p4)) → p1) ∧ (False → False))) → p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172925852854201072431198324175 : ((p3 ∧ (((((p3 ∨ p1) ∨ (True ∧ True)) ∨ p3) → (p2 ∨ (p5 ∧ p1))) ∧ p3)) ∨ (((False ∨ p5) ∨ (True ∨ p4)) ∨ (p4 → (p1 ∨ p5)))) := by
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
theorem thm_5_vars_49596252758199127323378850591 : (((((p3 ∧ p4) ∨ ((p2 → ((p1 ∧ (p5 ∨ True)) ∨ p5)) ∨ p3)) → ((p4 → ((False ∨ p1) ∨ True)) ∧ True)) → ((p5 → p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697579802643620018631074556690 : ((((False ∨ (p2 → (p2 ∧ ((False ∧ p4) → ((True ∧ True) → False))))) ∧ (((p5 → ((p3 ∧ (True ∨ p1)) ∧ (p1 ∨ p2))) ∧ p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38727401214309853493379080667 : (((((p3 ∨ p1) ∧ (p2 → (p1 ∨ p3))) → ((p1 ∧ (p2 ∨ (False ∨ True))) → ((p5 ∨ (False ∨ (p4 ∨ (p1 ∨ p5)))) ∨ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480727904081678556251065952408 : ((((((p4 ∧ False) ∧ (p1 ∨ p5)) ∧ (p1 → p4)) ∨ ((True ∨ p3) ∨ ((False → (False ∧ (((p2 ∨ p3) ∧ (p1 ∨ p3)) ∨ False))) ∧ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299155807338633762511745417493 : (False ∨ (((p5 ∨ ((((p4 ∨ ((p4 ∧ False) ∧ p1)) ∧ (((p4 → False) → p3) → p1)) ∧ (p1 ∧ (p4 ∨ True))) ∨ (True ∨ p3))) ∨ p1) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319192475088690114167359927710 : (p4 ∨ (((((((p5 ∨ p1) ∧ (p2 → p3)) → p5) ∧ (p5 → p1)) ∧ (p5 → (True ∧ p1))) ∧ p5) → (((p1 ∧ True) ∨ p1) ∧ (p1 ∨ p4)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113543419067888862255162016170 : ((((p2 → ((False ∧ p5) ∧ False)) → (p5 ∨ ((((p2 ∧ False) → p1) → (p1 ∨ (True ∨ (True ∨ True)))) ∨ p5))) ∨ (p1 ∧ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52004295912796152780651430753 : (((p1 ∧ (False ∨ (p2 ∧ ((p4 ∨ (p3 ∨ p2)) → ((p5 → p5) ∧ (p2 ∧ True)))))) ∨ (((p4 → False) ∧ (False ∨ (True → p4))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



