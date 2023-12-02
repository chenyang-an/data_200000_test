variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262248614076470979064245188162 : (True ∧ (((((((p4 ∨ (False ∨ (((p2 → p1) ∨ (p4 ∨ p2)) ∨ True))) ∧ False) → (True ∨ True)) → p1) ∨ p5) ∧ ((p2 → p5) ∧ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350350312737426722455139570511 : (p4 → ((p4 → (((p2 ∧ p2) ∧ ((False ∨ ((p3 ∧ p4) ∧ p3)) ∨ (((p4 → p5) ∧ (p5 → True)) → (False → True)))) ∨ (False ∨ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158351594251650310544420226075 : (((p5 ∧ p5) ∧ ((p3 → p4) ∧ (((p4 ∨ False) → p5) → (p2 ∨ (((True ∧ p4) ∧ p4) ∨ p4))))) ∨ (((p2 → p2) ∨ (p1 ∨ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347473373278959077016383049818 : (p3 → ((((True → False) ∨ (p2 ∧ True)) ∨ p2) ∨ ((False → ((p4 ∨ p3) ∧ True)) → (p5 → ((((p4 ∧ (p2 → True)) → p3) → p4) → p4))))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∧ (p2 → True)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119067158962330264059640961568 : ((p1 → (((p5 → (((p2 ∨ ((p1 ∨ (p2 ∧ True)) ∨ p1)) ∨ p1) ∧ p3)) → ((True ∧ (p1 ∧ p4)) ∨ p5)) ∧ (p2 → p1))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208130136451770183523331801475 : ((((p1 → False) ∨ p1) → (False → p4)) → ((p1 → ((((p5 ∨ True) ∨ p2) ∨ p2) ∨ p2)) → ((True ∧ (p2 → ((p5 ∨ p4) ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730129273811287966488555452917 : (((((p4 ∨ p3) → p1) → (((p1 → (((True → p2) → False) ∧ p4)) → p2) → (p1 ∨ ((p5 → p2) → (True ∨ (p5 ∨ (p2 ∨ p5))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244309427308828138711513467597 : ((False ∧ False) ∨ ((((p1 ∨ p1) ∧ ((p3 → (False → p5)) → ((((False ∧ True) ∧ ((p5 ∧ p5) ∨ p2)) ∧ (True ∨ p1)) → p2))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193259919564859807897369696466 : (((p2 ∨ (False → False)) ∧ (((p3 → p1) ∨ p3) ∨ p5)) → ((p1 ∨ ((p5 → (((p3 ∧ ((p3 → p1) ∨ p5)) → p5) ∨ False)) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
    cases h3
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135420471271065665838663677327 : (((False ∧ (((((p1 ∨ (p5 ∧ p2)) ∨ p4) → p4) → False) ∨ (p1 ∨ (p1 ∧ (True → False))))) ∨ ((True ∧ True) ∨ p5)) ∨ (p4 ∨ (p2 ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774050194116198644182173627614 : (((False ∨ ((((p3 → (((True → True) → ((p4 ∨ p1) ∧ p4)) ∨ ((p4 ∨ (p1 → p3)) ∧ p3))) ∨ (p1 → p3)) → p4) ∨ (p4 ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163027858586573426541420009541 : (((((False ∧ (p2 ∧ False)) ∨ p4) ∨ ((p3 ∨ False) → (p4 ∧ p2))) ∨ (p4 → (True ∨ p2))) ∧ ((p2 ∨ p3) → (p5 → (p2 ∨ (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158633943580122321060716303831 : ((p1 ∧ (((((p5 ∨ (p4 ∧ p3)) → True) → p3) → (((True ∧ p3) ∨ (True ∨ True)) → False)) ∨ False)) ∨ (((False → p1) ∨ (p1 ∨ p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197931156003709944705670984329 : (((p4 → (p2 ∧ p2)) → (False ∨ (True → p2))) ∨ ((((False ∨ ((p4 → p2) → (p2 → True))) ∨ (p4 ∧ p5)) → ((p2 → True) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153083726898454859061185975976 : ((p3 ∧ (True ∧ ((((False → p2) → p4) ∧ (p2 ∨ True)) ∧ (((p5 ∧ p3) → (p5 ∧ p3)) ∧ (p1 ∨ True))))) → ((p4 ∧ p5) ∨ (False → p1))) := by
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
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h7.left
    let h19 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178767346034305336129373316982 : ((((p1 → p2) → p5) ∧ (p4 → (p1 ∨ (p5 ∨ ((p1 → p1) ∨ p2))))) ∨ (((p3 ∨ (p2 ∨ p1)) ∧ ((True ∨ False) ∧ (p1 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115312163099546257425914057913 : ((((p4 → ((p1 ∨ (True ∨ p2)) → p1)) → (p5 ∧ False)) → (((((p4 → False) ∧ p2) ∧ p3) ∨ (p3 ∧ False)) → (p4 ∧ p1))) ∨ (False ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p4 → ((p1 ∨ (True ∨ p2)) → p1)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h14 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h15 := h6 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h17 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h18 := h6 h17
          -- False on the left can always be used.
          apply False.elim h18
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h8
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h29 : (p4 → ((p1 ∨ (True ∨ p2)) → p1)) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- Implications on the right can always be decomposed.
      intro h31
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h35 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h36 := h27 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h38 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h39 := h27 h38
          -- False on the left can always be used.
          apply False.elim h39
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h40 := h1 h29
    -- We need to get the right conjuct of h40 based on <expert-advice>.
    let h41 := h40.right
    -- False on the left can always be used.
    apply False.elim h41
  case inr h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h42.left
    let h44 := h42.right
    -- False on the left can always be used.
    apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304063600203045623699378444440 : (p1 ∨ ((p1 ∨ ((((p1 ∧ p3) ∧ (True → True)) → ((True ∧ ((p3 ∨ p5) ∨ ((p3 ∨ (p4 → False)) ∨ p3))) → p2)) ∨ (p3 → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199929638471212609712424180128 : ((((p5 ∧ True) → (p2 ∨ p5)) ∨ (p4 ∧ False)) → (((p5 ∨ ((p1 ∨ (p3 → (p4 ∧ True))) ∧ p5)) ∨ (False ∧ p1)) ∨ (True ∧ (False → p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112663898329932011914451719109 : ((((((p5 ∧ ((p5 ∨ False) → p1)) ∧ ((p4 ∨ p1) ∨ False)) ∨ ((p3 → (p4 ∨ p3)) → p5)) ∨ ((p5 → False) ∧ p5)) → p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171966786039618301781292219459 : (((True ∧ (p4 ∨ (((p3 ∧ p1) ∨ ((True ∨ p2) → False)) ∧ p4))) ∧ (False ∧ p1)) ∨ ((p1 → (p3 ∨ (False → (True ∨ (p1 → p3))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323268025863121633657852943893 : (p5 ∨ ((p3 ∨ ((False → p1) ∧ ((p2 ∨ p5) ∧ (p3 → (((False ∧ False) ∧ (True → (p2 → (False ∨ True)))) ∧ (p5 ∨ True)))))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200235415217545166465591403441 : ((((True → p2) ∨ True) → ((p5 ∨ p5) → False)) → ((((((((p3 ∨ p4) → ((p3 ∨ False) → p4)) ∨ p1) ∨ p4) ∧ p5) → False) ∨ False) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((True → p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p5 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : ((True → p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : (p5 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : ((True → p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (p5 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214140921643810789844767537028 : ((((p4 → False) ∨ True) → False) ∨ ((False ∧ p3) ∨ ((p1 ∧ (p3 ∧ (True ∧ ((False ∧ p3) ∨ p5)))) → (p3 → (((False ∨ p5) ∨ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51162632590869182245429366923 : ((((((((p3 ∨ ((False ∨ p5) ∨ p1)) ∨ p5) ∧ p2) ∧ p1) ∨ (True ∨ True)) ∧ (True → p5)) ∨ ((False ∧ (p5 ∨ p4)) → (p3 ∨ p4))) ∨ p3) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61041967684947467358478064615 : ((False ∧ (((p2 ∨ p5) → ((p3 ∨ ((False → p5) ∧ ((p3 ∨ p3) → p1))) ∨ ((((p4 ∨ p1) ∧ p5) ∧ True) ∧ p1))) ∨ (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355628767316676701969937133999 : (p5 → ((p3 ∨ ((p5 → ((p2 → (p1 ∧ p2)) → (p2 ∧ (p3 ∨ (((p5 ∧ p4) ∨ True) ∧ (p1 → (False → True))))))) → p4)) ∨ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61419495834805516972587652699 : ((p1 ∧ (((p3 ∨ (False ∨ ((((False ∧ (False ∨ p4)) → ((p5 ∨ (p2 ∨ (p3 → p4))) → p3)) ∧ p5) ∧ (True → p5)))) → p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119311486903556739648639305401 : ((p3 → ((((((p4 → p5) ∨ p3) ∧ (((p1 → (p5 ∨ p2)) → p2) ∧ False)) ∧ (p3 → p4)) ∨ True) ∧ ((p5 → p4) → p3))) ∨ (False ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53003028936110566728133122019 : (((((((p5 ∨ p2) ∨ p3) ∧ True) ∨ p5) ∧ ((p2 ∧ False) ∨ False)) ∧ ((False → (p1 → p1)) ∨ (True ∧ (((True → False) ∧ p2) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313241387835758674706807986082 : (p3 ∨ (((p3 ∨ p4) ∨ (((False ∨ ((p4 ∧ p1) ∨ p3)) → ((p3 → False) ∨ (p2 → ((p1 ∧ p1) ∨ ((p5 → p1) → p3))))) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316488191395359452504418651247 : (p3 ∨ (p2 ∨ ((((((False ∨ p1) ∨ (p4 → (p3 → p1))) ∨ ((p5 ∧ p5) ∨ (True → p4))) ∧ p3) → (((p3 ∨ p4) ∧ False) ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61387854913145488620414302256 : ((p1 ∧ ((((p2 ∧ ((p1 → p2) → ((True ∨ (p5 ∨ False)) ∧ True))) ∧ True) ∧ (p4 → (((p3 ∨ p2) ∨ p4) ∧ (p5 ∨ p5)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336117569430482069927572486303 : (p1 → (((((p5 → (p5 → p4)) → (True → (p2 ∧ ((((True → p4) → p5) ∨ p4) ∧ (p2 → (p3 → p1)))))) ∨ (p2 ∨ True)) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200023494005707133387342758979 : ((((True ∨ p2) → (p5 ∧ True)) → (p3 ∧ p5)) → (False ∨ (((p4 ∨ p3) ∧ (True → (p3 ∧ (True ∧ p2)))) ∨ (p2 → ((True ∧ False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259240336016928500956149978074 : ((False → False) → (p3 → (((((False ∧ ((p5 → (True ∧ p2)) → p1)) ∧ p5) ∨ ((True ∧ p3) → p5)) ∨ (p3 ∧ p2)) ∨ (p5 ∨ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307814892144267059914428293372 : (p1 ∨ (p4 → (((False → (False → True)) ∧ (True ∨ True)) → (((p3 ∧ (((p4 ∨ p3) ∧ p4) ∧ p2)) ∧ p4) → (((True ∨ p5) ∧ False) ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h2.left
    let h14 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h2.left
    let h19 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172389379609299542159260221191 : ((((p3 → (p5 ∧ True)) ∧ (p4 → p2)) → ((False ∨ p5) ∨ (p5 ∨ (p2 → True)))) ∨ (p5 ∧ (True ∨ (True → ((True ∧ (False ∨ p5)) → p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177646475397849124560672453723 : ((((((True ∧ ((False → p5) → p1)) ∨ (p3 ∧ False)) ∧ p4) ∨ True) ∧ p4) ∨ ((True → (p2 ∨ ((True ∧ (False ∧ False)) → (p4 → p3)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246364665608303929023480864259 : ((p4 ∧ p5) ∨ (p2 → ((False ∧ (False ∨ (p5 ∧ (((p2 ∧ p4) ∨ (((True ∧ ((p2 ∨ False) → p3)) ∨ p1) ∨ (p2 ∧ p2))) → p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656952900061770718385909078359 : ((((((p1 → (True ∨ p4)) ∧ p2) → (((((False ∧ (False → False)) ∨ (p5 ∨ p2)) → (p2 ∧ True)) ∨ (p2 → p1)) → p5)) ∨ (False → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117590681291537646951609457908 : ((p2 ∧ (p4 ∧ ((((((True ∨ (p3 → p4)) ∨ p1) ∨ (p3 ∧ p1)) → p3) ∧ (p4 → (p3 → (p5 ∧ (p1 ∨ p5))))) ∨ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66735783236210892279286487378 : ((True → ((False → p4) → ((((True → p2) ∧ (p1 ∨ p2)) → (p5 ∨ (p1 ∧ p1))) → ((True ∨ True) ∧ ((p4 ∨ (p1 ∨ p4)) ∨ True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306170419727993774065586329006 : (p1 ∨ (((False → p2) → False) ∨ (((p5 ∨ ((p3 → (p4 → (((p2 → p2) → p5) ∧ (p4 ∧ (True → p2))))) ∨ p3)) ∧ p3) → (False ∨ p3)))) := by
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
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254292875427203064755157835821 : ((p2 ∧ p3) → ((p4 ∧ ((p1 ∧ p4) ∨ ((((p1 ∧ False) ∧ p2) → p2) → p3))) → (((p5 ∨ p4) ∧ (False ∨ True)) ∧ ((p5 ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h8 := h1.left
    let h9 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h1.left
    let h29 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h1.left
    let h32 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312321332505188019155953091109 : (p2 ∨ (p2 → ((p4 → (False ∨ p1)) → ((((((True ∧ (p4 ∧ (p5 ∨ (p1 ∨ p4)))) → p5) ∨ (p4 → (p4 → p3))) ∧ p3) → p4) ∨ p2)))) := by
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
theorem thm_5_vars_157554474209559056654654417514 : ((((p2 → ((False ∨ False) → ((p4 → (p3 ∨ (p3 ∨ p3))) → p2))) ∨ (p3 ∨ p1)) → (p4 ∨ p4)) ∨ (p3 → (True ∨ (p2 ∨ (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704880026057418844711540095963 : ((((p2 ∨ ((p3 → p4) → (p2 → ((p3 ∨ True) ∨ p2)))) → ((True ∧ p5) → (((False ∨ False) ∨ p4) ∨ (p5 → ((p2 → True) ∨ p4))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116794572538779808379728630201 : (((p2 ∨ p1) ∨ ((((((False ∧ True) → p5) ∧ p2) → False) → False) ∧ ((p4 → p1) → ((p3 ∨ p1) ∨ ((p5 → p2) ∨ p3))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326292624798823577266381602925 : (p5 ∨ (p4 → ((p2 ∨ (((p2 → (p4 ∨ (p5 ∨ ((p2 ∧ p5) → (p1 ∧ p1))))) ∨ p3) ∧ ((p2 → p2) → (p1 ∨ p5)))) ∨ (p4 ∨ p2)))) := by
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
theorem thm_5_vars_54093951922496057734282541228 : ((((p4 ∨ p1) → ((p5 ∨ True) ∨ ((p4 ∨ p5) → p4))) → (((p4 → (False ∧ (p3 → (p1 ∨ p4)))) ∧ False) ∨ ((p2 ∧ p3) → True))) ∨ p2) := by
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
theorem thm_5_vars_217280856925236233056464838270 : (((p3 ∧ (p4 ∧ p5)) ∨ True) → (((p1 ∧ p5) ∨ ((p1 ∧ True) → (((p5 ∧ (p1 → p5)) ∨ p1) ∧ (p4 ∨ (True ∨ p4))))) ∨ (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
    -- Conjunctions on the left can always be decomposed.
    let h16 := h13.left
    let h17 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44763098382121811234381193586 : ((((((True ∨ True) → p4) → False) → ((((p1 → (p3 ∧ (p5 ∧ (((p5 → True) → p4) ∨ False)))) → p2) → True) ∨ (p3 → True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141308188574493044134820417761 : (((p5 ∨ (True → (p3 → p4))) ∧ (((True ∧ p5) ∨ (p1 → p2)) ∨ (((p1 ∧ False) ∨ p1) ∨ (p4 ∨ (p1 ∨ p2))))) → ((p1 ∨ True) ∧ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h36
          case inr h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612860660819890428539708575797 : (((((p3 ∧ (((p4 ∨ (((True ∨ True) ∨ (p3 → p1)) → (False ∧ False))) ∧ (p3 ∧ p1)) ∧ (p4 → (False → p5)))) ∨ (False → True)) ∨ p5) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46854006508406389172120381787 : (((((p1 ∨ p3) → ((p3 ∨ ((True ∧ True) → (p1 ∧ (p2 ∨ (p5 ∨ p4))))) → (False ∧ ((True ∧ p2) ∧ p4)))) ∧ True) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345346663694209880791610176270 : (p3 → (((p4 ∨ (False ∨ (p3 ∧ ((False → (p1 ∨ ((p1 → p4) ∧ False))) → ((p4 ∧ (p3 ∨ ((True → True) ∧ True))) → p5))))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704063465505377364426437789524 : (((((p2 ∧ (((True ∧ p5) ∧ (p1 → p3)) ∧ p2)) → False) → ((p1 ∧ ((p3 ∧ ((p1 ∨ True) ∨ (p2 ∧ p3))) ∧ True)) → (p3 ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609776081985993742874685675534 : (((((p5 ∨ (((p5 ∨ True) → ((p1 ∨ (p5 ∧ p5)) ∨ (p1 → (p4 ∧ (((p4 ∨ False) ∧ False) → p4))))) → (p3 ∨ p3))) ∨ p3) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_639779992607361177098783153758 : ((((((False ∨ p3) ∧ p4) ∨ ((((p4 ∧ p3) ∨ (p4 ∧ (False ∧ True))) ∨ (((p1 ∨ (p2 ∧ p1)) → False) → (p2 → p1))) ∨ p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217201258742893430322622192428 : ((((p4 ∨ False) → False) ∨ p1) → ((p3 ∨ p2) ∨ (((p5 → True) → p5) → (True ∧ (p3 ∨ (p5 ∧ ((((p4 ∧ True) → p1) → p1) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∧ True) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44977923308496945176878238204 : ((((p2 → True) ∧ (((p3 → p3) → True) → ((p4 ∧ p4) ∨ (p2 ∨ (False → ((((True ∧ p4) → True) ∧ (p4 → False)) ∨ True)))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178239700861935825089042796955 : (((((((p3 ∧ p5) ∨ (False → p2)) ∧ p1) ∨ p2) ∧ False) ∧ (p4 ∧ False)) ∨ ((True ∧ (p1 ∨ (p3 → (p5 → (p4 ∧ (p4 ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228772357502284903060574715760 : ((p3 ∨ (p3 ∧ True)) ∨ (((False → (p1 → p5)) → p2) → (p5 → ((((p3 → p4) ∨ ((p1 ∨ p3) → p1)) ∧ p2) ∨ ((p2 → p4) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p1 → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61459121267276458694972563112 : ((p1 ∧ ((p4 → (True ∧ ((p2 → ((p3 ∨ ((True ∧ p5) → ((p2 ∨ p1) ∨ False))) → False)) ∧ (False ∧ (p4 → p1))))) ∧ (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324640671024448503389352818470 : (p5 ∨ (((False → p3) ∧ p3) ∨ ((((((False ∨ p2) ∨ p2) ∨ p1) ∧ (p2 ∨ (p1 → p4))) → ((p1 ∨ False) ∨ (False → (p1 ∨ p4)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157856248860485676002383868028 : ((((p2 ∧ False) → ((True ∨ p3) → (p5 → (p1 → True)))) ∧ (((False ∧ p1) ∧ False) ∨ (p4 ∧ True))) ∨ ((True → False) ∨ ((p2 ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149507286976755901073060166674 : ((p1 ∧ ((((p2 → p4) ∧ (p5 ∨ p2)) → (True ∨ (p2 → p4))) → (((p1 → (p4 → p3)) → p4) ∧ p4))) ∨ (True → (True ∨ (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53186325117151490514219771007 : ((((p3 → ((((True ∧ False) ∨ (p4 ∧ p5)) ∧ p5) → True)) → p5) ∨ ((False → ((((p1 ∨ p5) ∨ p5) → False) ∨ False)) ∨ (p2 → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251117850077181485128709582494 : ((p2 → False) ∨ (((((False ∨ ((p1 → ((p5 ∧ p2) ∧ False)) ∧ False)) ∨ False) ∨ (((False ∨ p1) ∨ p1) ∨ (p5 ∨ True))) → (True → p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ ((p1 → ((p5 ∧ p2) ∧ False)) ∧ False)) ∨ False) ∨ (((False ∨ p1) ∨ p1) ∨ (p5 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717114360750767563302585889519 : ((((False ∨ ((p2 ∧ p4) → p1)) ∧ ((((True ∨ (p3 → True)) → False) → ((p3 → False) ∧ True)) ∧ ((p5 ∧ ((False ∧ False) ∧ p2)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185432406350002806740007124125 : ((False ∨ ((((p4 ∧ (False ∧ (False ∧ p1))) → p2) ∨ False) → p3)) ∨ (True → (False → (p2 ∨ (((p2 ∧ p4) → (False ∨ (p5 → p4))) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118639920364893680903683675425 : ((p4 ∨ ((p4 ∧ p1) ∨ (((p3 ∧ True) → (((False ∧ p4) ∨ ((p4 → (((p2 → p1) → p1) ∧ p4)) ∨ p2)) → p1)) ∨ True))) ∨ (False ∨ p2)) := by
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
theorem thm_5_vars_232171962001091388860817051000 : (((True → p5) → p3) → ((p5 ∨ (p1 ∨ p5)) ∨ ((((p2 → ((p5 ∨ p3) ∨ p5)) ∧ p1) ∨ (p4 → p4)) ∧ (p4 → ((p4 ∨ p1) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48413630744604130351103356746 : (((p2 → ((True ∧ (((False → ((p5 ∨ True) ∨ p1)) ∧ (p4 ∧ p2)) ∨ (p5 → False))) ∨ (p4 ∨ (p4 ∧ (p2 → p4))))) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66145077050992726497578668248 : ((p5 ∨ ((p3 ∨ ((p4 → ((True ∨ ((((p3 ∨ p4) ∨ (p2 → True)) ∨ (p3 → p4)) → p3)) ∧ (p3 ∨ p5))) → False)) ∨ (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167464729652318100308688771309 : (((p2 → (((p4 → p5) → (((True → False) ∨ (p2 → p5)) ∨ (p3 ∧ False))) ∨ p2)) → p3) → (p5 ∨ (p3 → ((p3 ∧ (False → p3)) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245367517613072300588687470789 : ((p2 ∧ p3) ∨ (((((False ∨ p5) ∧ p1) ∧ (True ∨ p4)) ∨ p5) ∨ ((p4 ∧ p2) → (p2 → (p2 ∨ (((True ∧ p2) → (p5 ∧ p2)) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147514748086247792982717104210 : (((p3 ∨ (p3 → (((p4 ∨ ((False ∧ p5) ∧ False)) → (False ∧ True)) ∧ ((p1 ∨ p5) → (p2 ∨ p5))))) ∨ True) ∨ (((False ∨ p4) → p2) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39178871536148376323040129520 : ((((p1 → p3) → (((p1 → ((p2 → p2) → (((False ∧ p1) ∧ p4) ∨ (((p4 ∧ (True ∧ p4)) ∨ p5) → False)))) → p2) ∨ p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134474597218452545577179446063 : ((((p4 ∨ (p3 → (False ∨ ((((p4 → (True ∨ p3)) ∧ p3) → p5) ∨ ((p3 ∧ p4) ∧ (p1 ∨ p2)))))) ∧ True) → p2) ∨ ((p3 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57340668793314992381097541797 : (((p2 ∧ (p2 ∧ p1)) ∨ ((((True → (p2 → (((False ∨ p2) → ((p2 → p5) → True)) ∧ p2))) ∨ p1) → False) → (p1 ∨ (p2 → p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p2 → (((False ∨ p2) → ((p2 → p5) → True)) ∧ p2))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353534685552205782097241729714 : (p4 → (p3 ∨ (((p3 ∧ p4) ∨ ((((((p4 → p3) ∧ p4) ∧ p4) ∧ p5) ∧ p5) ∨ (p2 → ((((True ∨ False) ∧ p5) ∧ False) → p4)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179660099824798684993127180366 : ((p5 → (((False ∨ p1) → p3) → ((p3 ∨ ((p5 ∧ False) ∧ p5)) → False))) ∨ ((p5 ∧ (p3 → True)) → (p4 → (True ∨ ((p4 ∧ p1) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299225127793873507007373831232 : (False ∨ ((((((p3 ∧ True) → True) ∨ ((p3 ∧ ((p3 ∨ (False → ((p2 → True) → False))) ∨ p5)) ∨ p1)) → (p2 ∨ p5)) → (p4 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66531627803969324444898645622 : ((True → (((p5 ∨ (True ∧ ((p1 ∨ p2) ∧ p5))) ∧ (((False ∧ p4) ∨ ((p1 ∧ p5) ∨ ((True ∨ (p4 ∧ True)) ∨ p4))) → True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61178813668368136531080333904 : ((False ∧ ((p4 → (True ∨ p4)) → (p4 ∨ (False ∧ (p4 ∨ ((True → (False ∧ True)) ∧ (((((p5 ∨ False) ∧ p4) ∨ p3) ∨ True) → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66462596758429231911301686684 : ((True → ((p4 ∧ ((True ∧ ((False ∨ ((p2 ∧ True) ∧ (p4 → (((p1 ∧ p5) → (p4 ∧ (p5 → False))) ∧ p1)))) ∧ True)) → False)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686822830923787300033908341403 : ((((p4 ∧ ((((False → (p2 → p5)) → p3) → ((True → (False ∧ p2)) ∧ p4)) → (p3 → p4))) → ((p5 ∧ (True ∨ (p3 → p2))) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_301599279467480868984404450021 : (False ∨ (((p1 ∨ p1) ∨ p2) → (((p5 → p2) ∨ p5) ∨ ((((p5 ∨ True) ∨ (((p4 ∨ p2) ∨ p2) → (p1 → p1))) ∧ (False → p4)) ∨ p4)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116706238480748895362546769346 : (((p1 ∧ p1) ∨ ((((p2 → (p1 ∧ (p2 ∧ (True ∧ p3)))) → ((True ∧ True) → (p4 ∧ True))) → p1) → (p1 → (False ∧ True)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207134562281942376584241818245 : (((True → ((p5 ∧ False) → True)) ∧ p2) → (p3 → ((((p4 ∨ (p3 → (True → (p4 ∧ p2)))) ∨ p1) ∨ ((p3 ∨ True) ∧ (p2 ∧ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183864287897490044658071039155 : (((((True → (p1 → p5)) → p1) ∨ (p3 ∨ (p4 → False))) ∧ p4) ∨ (((p5 ∧ p1) ∧ True) → ((p2 → p4) ∨ ((p1 ∧ True) ∨ (p5 ∧ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66064531655495255148344136231 : ((p5 ∨ ((((False → p3) ∧ (((True ∨ ((p5 ∧ p5) ∨ p4)) ∨ p3) → False)) ∨ (p4 → (((True ∧ (p4 ∨ p5)) ∧ False) → p1))) ∨ p2)) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180089895287215003482728415877 : (((((True ∨ ((True → p2) ∧ (p5 ∧ p1))) ∨ (p3 ∧ p3)) ∧ p4) → p3) → (((p3 ∧ p3) ∧ p4) ∨ (((p2 ∧ p2) ∧ False) ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_307649526624466172324164726159 : (p1 ∨ (p1 → (False ∨ (p4 → (((p5 → p4) ∧ (p1 → (p5 → ((p1 → p2) ∧ p1)))) → ((p4 ∧ p3) ∨ ((p4 → (p2 ∨ p1)) ∧ True))))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184802334553868919702279648226 : (((False ∨ (p1 ∨ (p3 ∨ p2))) ∨ (p3 ∧ (True → (p3 ∨ True)))) ∨ (True ∨ ((p4 → (p5 → p2)) → (((False ∨ p1) → (p3 ∨ p2)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609085111420474845035450830329 : ((((((((p2 → p2) → p5) ∨ (p1 ∨ False)) ∧ (((p5 ∨ p5) ∧ p4) → (((p4 ∨ ((p1 ∨ p2) ∧ p5)) ∧ p5) → p5))) ∨ False) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317970872406129199199219613107 : (p4 ∨ ((p1 → (((((p3 → (False → (True → p2))) ∧ (((p4 → True) ∧ ((p4 ∧ False) ∧ True)) ∨ (p2 ∧ p5))) ∧ False) ∨ p1) ∨ p1)) ∨ p1)) := by
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
theorem thm_5_vars_113653709145987131216225210276 : (((((p5 ∧ p5) → (p1 ∧ (p2 ∨ (p1 ∧ (((p3 ∧ (p1 ∨ p2)) → p1) ∨ ((True ∧ p3) ∧ p5)))))) ∧ p1) → (p3 ∨ p3)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



