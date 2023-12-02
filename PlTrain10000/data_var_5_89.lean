variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776386716653884463810117370215 : (((p1 ∨ (((((p3 ∧ ((False ∨ (p3 → p2)) ∨ (p5 → (p4 → True)))) ∨ (((p3 ∨ p5) ∧ (p3 ∧ p5)) ∨ False)) → p1) ∧ p1) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_231895510729183171620968369977 : (((True ∨ p5) → p2) → ((p2 → (((True ∨ (True → (True ∧ False))) ∧ p5) → (p5 ∧ p1))) ∨ (True → (True → ((p5 ∨ (False ∨ p3)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238028473613431775083357799419 : ((True ∨ p1) ∧ ((p1 ∨ p2) ∨ ((p2 → ((((False ∧ (p3 ∨ (True → (True ∧ p2)))) ∨ p4) ∨ False) ∨ (p2 ∨ (p2 ∧ p4)))) ∨ (False → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65770048380148103111750362936 : ((p4 ∨ (((True → ((p4 → p3) ∧ p5)) ∨ (((False ∨ (p3 ∨ (p5 ∨ p5))) ∧ False) ∨ p3)) ∨ ((True ∧ p1) ∨ (p2 ∧ (p3 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338203306127530839058079454398 : (p1 → (((p2 → True) ∧ ((p2 ∨ True) ∧ p1)) ∧ (p2 ∨ (((False ∨ (p1 → False)) ∧ p3) ∨ ((p2 ∨ (p4 ∨ ((p5 → p5) ∧ True))) ∨ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197955213003121532165331524630 : (((p3 ∧ p3) ∧ (p5 ∧ ((True → p3) ∧ False))) ∨ (((p1 ∨ False) ∧ ((False ∨ True) → ((True ∧ True) ∧ (False ∧ (p2 ∧ p1))))) → (True ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62627170793567428414140348665 : ((p4 ∧ ((((p4 → p1) ∧ ((p1 ∧ p2) → p5)) ∨ (True ∧ (((False → False) → (((p3 ∧ (p3 ∨ p2)) ∨ True) ∨ p3)) ∧ True))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699426663689659584938583714411 : ((((((p3 ∨ (True → ((p3 ∧ (p2 → p1)) ∨ p1))) ∧ True) ∨ p2) → ((p1 ∨ p1) ∧ (p5 ∨ (((p4 ∨ (p3 ∧ p3)) ∧ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172717166352298038164671299117 : (((p4 ∨ p5) ∨ ((True → ((False → (False ∧ (True → p2))) ∧ (p4 → p5))) → p1)) ∨ (True ∨ (((((False ∨ p4) ∧ False) ∧ p1) ∧ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177939921898471593281006121504 : (((((p5 → p1) → False) ∧ ((True → (False ∨ p5)) → (p3 → p3))) ∨ False) ∨ ((p2 ∨ ((p3 ∧ p1) ∨ p3)) → ((p5 ∨ p4) ∨ (p2 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245890618849198532618929353709 : ((p3 ∧ p5) ∨ (((((False ∨ p1) ∧ p3) ∨ (p5 → True)) ∨ (False ∧ ((False ∧ (p5 ∨ ((False ∨ ((p1 ∨ p1) → p5)) ∨ p5))) → p2))) ∨ False)) := by
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
theorem thm_5_vars_319261016397153736144416678855 : (p4 ∨ (((((p1 ∨ (p1 ∧ ((p3 → True) → (True → p4)))) ∧ (p2 ∨ False)) ∧ True) ∧ p3) ∨ (p1 ∨ (True ∨ (True → (p4 → (p2 ∨ p3))))))) := by
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
theorem thm_5_vars_702062689648275412172019542217 : ((((p1 → ((False ∧ (p2 ∨ ((p2 ∨ p4) → p3))) ∨ p4)) ∧ ((True ∧ ((p4 ∨ (p1 → False)) ∨ (p5 ∧ (p4 → (p2 ∨ p5))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40317867066291339688574652311 : (((((p5 ∧ ((p1 → (((p1 ∧ (p4 ∨ (p5 ∨ p5))) → p2) ∧ ((p5 → p4) ∧ p3))) ∧ ((p4 ∧ p2) ∧ False))) ∧ p4) ∨ p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75866322336037337434055712235 : ((((p1 ∨ (((p5 ∨ p4) ∨ ((((p1 ∧ p1) ∧ ((p5 → p3) → p4)) ∧ ((p2 → (True → True)) ∧ False)) ∧ False)) ∨ p2)) ∨ True) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (((p5 ∨ p4) ∨ ((((p1 ∧ p1) ∧ ((p5 → p3) → p4)) ∧ ((p2 → (True → True)) ∧ False)) ∧ False)) ∨ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776615491117971518804411685498 : (((p1 ∨ ((p1 ∨ (p5 ∨ (p1 ∧ ((((True ∧ p2) ∨ True) ∧ (((p4 → p5) ∨ True) ∨ p5)) ∨ (p5 → (p3 ∧ (p5 ∧ p2))))))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_308573697952000994017722425726 : (p2 ∨ (((((p3 ∧ True) ∨ p4) ∧ False) ∨ ((p3 → False) ∧ ((((((p1 ∧ p4) → False) ∧ p2) ∨ p4) → p4) ∧ (p4 ∧ (True ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315645119145522417294592189450 : (p3 ∨ ((False ∧ p2) ∨ ((p4 ∨ (((p3 ∨ p1) ∨ ((p1 ∧ True) ∨ p4)) ∨ (p4 ∧ p3))) ∨ (True ∨ ((True ∨ p2) ∧ (p3 ∨ (p1 → p4))))))) := by
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
theorem thm_5_vars_429472751221965604703788338870 : ((((((p1 ∧ (p4 → p3)) ∨ ((False → (p4 ∧ False)) → (p5 ∨ (False ∧ (p3 ∧ p2))))) ∨ ((p1 → (p3 ∧ p3)) ∨ True)) ∨ (p4 ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175346302849098208221484012494 : ((p5 ∨ (((p3 ∨ (p3 ∨ p4)) ∨ (True → ((p4 ∨ p4) ∨ p3))) ∧ (False → p3))) → (p4 → (p2 ∨ (False ∨ ((p2 ∨ False) → (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68664349249624752588135188213 : ((p4 → ((True ∧ ((p3 → (((p2 ∨ (False ∧ p4)) ∨ p3) ∨ (False ∧ (True ∨ p5)))) → ((False ∧ ((True ∧ True) ∨ True)) → p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42438009902765645898889372157 : (((p5 ∧ (p4 ∧ ((p1 ∨ (True ∨ ((p1 ∨ (((True ∧ p5) ∧ (p1 ∧ (p1 → False))) ∧ p4)) ∧ (p5 ∨ (p4 → p2))))) ∧ p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184515960339130331640368209866 : (((p5 ∧ ((((p2 ∨ p5) ∨ p3) ∨ p5) → p5)) ∨ (p2 ∧ p1)) ∨ (True ∨ ((p4 ∧ (p4 → p3)) ∧ ((p3 → p1) ∨ ((False ∧ p1) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247908057155389520967098854043 : ((p1 ∨ p3) ∨ (((p1 ∧ (p3 ∧ ((p3 ∨ p4) ∨ True))) ∨ ((((p5 → (p5 → False)) ∧ False) ∧ (True ∧ p5)) → p5)) ∧ (p4 ∨ (False → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310630814514556735489709311628 : (p2 ∨ (((True → p2) → (p5 ∨ p1)) ∨ ((((p5 ∧ (p1 ∧ (((p1 ∧ (p3 → False)) ∨ p2) ∨ p5))) ∧ False) ∧ (p1 → False)) → (p3 → False)))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
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
      apply False.elim h6
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347652952622792061319951552778 : (p3 → (((p2 → (p1 ∧ False)) → p2) → (((((p2 → True) ∧ p5) ∨ p3) ∧ (p4 ∧ p4)) ∨ ((p1 ∨ ((p5 → False) ∧ (p3 ∨ p3))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41204818258634977262818145770 : ((((p3 ∨ ((((p2 ∨ ((True ∨ True) → (p1 → (p3 ∨ True)))) ∧ p3) ∧ (True → p3)) → (True ∨ False))) → ((p5 ∧ p5) → False)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314456745183027509741097853930 : (p3 ∨ (((((((True → p5) ∧ (((p2 ∨ p3) → True) ∧ p2)) ∨ (p1 ∨ True)) ∧ p1) ∧ (p2 ∧ p3)) → p4) → (((p4 ∧ p3) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_106985068465594218280387643273 : ((((p2 → p5) ∧ (p3 ∨ p4)) ∨ (p3 ∨ (((((p5 ∧ p4) ∧ p5) → (False ∨ (p5 ∧ (p3 ∨ (p2 ∨ p1))))) ∨ p3) ∨ True))) ∧ (p5 ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659153150422094096940488371166 : ((((p3 → ((p5 ∨ ((False ∧ p3) → ((p1 ∨ ((p5 → False) ∨ False)) → p2))) → ((p3 ∧ (p4 ∨ p1)) ∨ (p4 ∨ p4)))) ∨ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617895708181051883160296850859 : ((((((False → p3) ∨ (p4 → (True ∧ p3))) → ((((p5 ∧ ((p2 ∧ (p5 → p2)) ∧ True)) ∨ (p4 ∨ (p4 ∨ p2))) ∧ p1) ∨ p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_135086046136695948362366311342 : ((((((p5 → False) ∧ (((p1 → (p1 ∨ True)) ∧ p4) ∨ p5)) → p5) ∨ ((p5 ∨ (p3 ∨ True)) → True)) ∨ (p2 → p5)) ∨ (p2 ∧ (p5 ∧ True))) := by
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
theorem thm_5_vars_112444864254019043758132076988 : ((((((p5 ∨ (p4 ∨ (p4 → p5))) ∨ ((p1 ∨ (((p5 ∨ (False ∨ p1)) ∨ (p5 ∧ p1)) → p3)) ∨ p2)) → False) ∨ p2) → p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55557376283125593628119954159 : (((p3 ∧ ((p4 → p2) → (p4 ∧ True))) → (((((((p4 ∨ p5) ∧ (p4 → p3)) ∧ p2) → p5) ∧ (p4 ∨ False)) → (False ∨ True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346930305322338847054551328078 : (p3 → (((((p5 ∧ p3) → ((((p1 ∧ p1) → (p3 → (p4 → p3))) → p2) → False)) → True) ∧ p5) → (((p2 ∧ (p2 → False)) ∧ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180525595552236243239692543185 : (((((p3 ∧ ((False ∧ p3) ∨ False)) ∨ True) → False) ∨ ((False → False) ∧ p5)) → (p4 ∨ (((p2 ∧ p1) ∨ ((p1 → True) ∧ (False → p5))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p3 ∧ ((False ∧ p3) ∨ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111074509259981317540701462897 : ((((((((p3 ∧ (True → p5)) → p4) ∨ p4) ∧ (p1 ∧ True)) ∨ (p2 ∨ p3)) → (True ∧ (((p3 ∨ p5) → False) ∧ False))) ∧ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60617513306119432735244371312 : ((True ∧ ((p2 ∧ ((((p2 → (p5 ∨ ((False → p5) → p3))) → p3) → (True ∨ True)) → (p4 ∨ (p3 ∨ (p2 ∧ p1))))) ∨ (True ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_37463970792433906155905126440 : (((((True ∧ (p3 → (((p4 ∨ p2) → p1) ∧ p4))) ∧ (p3 ∧ ((True ∨ ((p1 ∨ ((p2 ∨ p1) ∧ p5)) ∨ p2)) → p2))) ∨ p3) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69141809231266058377990125178 : ((p5 → (((p2 → (((((False → (p3 ∧ p3)) → p4) ∧ ((True ∨ p1) ∧ p5)) → p1) ∨ p4)) → (p2 ∧ p5)) ∨ (True ∧ (p2 → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172859698064161459659637443678 : ((False ∧ (p1 ∨ (p1 ∨ ((p2 → (p3 ∨ ((p4 ∧ p1) ∧ p3))) ∧ (True ∧ p5))))) ∨ (False → ((((p1 → p5) ∧ p5) ∨ p3) ∧ (p1 → p3)))) := by
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
theorem thm_5_vars_682663837591637362255185444536 : (((((((p1 ∨ True) ∧ (p4 → p3)) ∨ p5) ∨ ((p3 ∨ False) → (((False → False) ∨ p5) ∨ p3))) ∧ ((p4 ∨ ((p5 → True) ∧ p5)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397115623865688784611509637333 : ((((p1 ∨ ((((((p4 ∧ ((p1 → p4) ∨ True)) ∨ (True ∧ False)) → ((p3 ∨ True) ∧ p5)) → (p3 ∧ (p1 ∧ p2))) → p1) ∧ p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_4105706912888359380720748890 : (p3 ∨ ((((p4 ∨ (p1 ∧ p3)) ∧ p1) → (p3 → (((p5 ∨ p5) → False) → p2))) ∨ (False → (p4 → (p4 → ((True ∨ p5) → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198211632524657264387252929754 : (((p5 → p1) → ((p5 ∨ (p1 ∨ p5)) ∧ p4)) ∨ (((True ∧ ((((p5 ∨ p1) ∧ p3) ∧ p2) ∧ ((False ∧ p3) ∧ p1))) ∨ (p2 ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303713660168517538173596723718 : (p1 ∨ (((((True ∧ (p5 ∨ (p2 ∨ p2))) → (((p1 → (p2 → (p4 ∨ (p4 → p5)))) → p4) → ((p2 ∧ p2) ∧ p5))) → p5) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213356328305941989676437902401 : (((p4 ∧ (p3 ∧ True)) ∧ p2) ∨ ((((p1 ∧ (p5 ∨ (p5 → p5))) ∨ (True ∧ p5)) ∨ (True → True)) ∨ ((p5 ∧ ((p3 ∧ p2) ∨ True)) → p1))) := by
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
theorem thm_5_vars_44277466537344194963845718388 : ((((False → (True ∧ ((p4 ∨ ((True → (p1 → True)) ∨ True)) ∨ ((p3 ∨ (p2 → p5)) ∨ True)))) → ((p1 → True) ∨ (p3 ∧ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3371209015989046975169005878 : ((True → False) → ((p3 ∨ (False ∧ p1)) ∨ (((True ∨ ((p3 → (p3 ∨ p3)) ∧ p5)) ∧ (p1 ∨ (((False → p4) ∧ p1) ∨ p4))) → p4))) := by
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
theorem thm_5_vars_119392064592120175625431018173 : ((p4 → (((((((p2 ∨ p1) ∧ (p4 ∨ p3)) ∨ p2) ∧ (p1 ∧ p2)) ∨ p5) → (p5 ∧ (((p4 ∧ p4) ∧ p2) → p3))) ∧ p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318599464038519295571456814440 : (p4 ∨ ((((((True → p4) ∧ ((p5 → p5) ∧ p3)) ∧ True) → False) ∧ (((p3 ∧ ((True → False) → p1)) ∧ (p1 ∧ p2)) ∨ p2)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217836410832442347497007866189 : (((p4 ∨ (True → p1)) → p5) → (((p5 ∧ ((p1 ∧ (p5 ∨ p2)) ∧ (p3 → p5))) → (((True ∨ p5) → p5) ∨ p2)) ∧ ((True ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745673490255921253115544409906 : ((((True ∨ p4) → ((False → (((True ∨ (((True ∧ (p2 ∧ True)) ∧ ((p2 ∨ True) ∨ p3)) → True)) → (p1 → (p4 ∧ p3))) → p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9178257694792456060513793574 : ((((((p1 ∨ (False ∨ p3)) ∨ p4) ∧ ((p1 ∧ p2) → p4)) ∨ ((((True ∧ p2) ∧ False) → ((p5 → p3) ∧ True)) ∨ (True ∨ p1))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_152451479059335039931039420479 : (((p2 ∧ (True ∧ p2)) ∧ (p2 ∧ ((((True ∧ True) ∨ (((p3 ∧ False) → True) ∨ p3)) ∧ p2) ∧ (p3 ∨ p3)))) → ((p1 ∧ p4) ∨ (False ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678108572904556210756120360285 : ((((((False ∨ ((p4 → False) ∧ ((p5 ∨ p2) → p5))) ∧ (False → False)) ∧ ((p4 ∧ (p1 ∨ False)) ∨ p5)) ∨ ((p3 ∨ (p5 → True)) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_747761112916908454431749856482 : ((((False → p1) → ((((((False → p4) ∧ ((p4 → ((p4 ∨ True) ∨ False)) → False)) → ((False ∧ p3) ∨ True)) → p4) ∨ True) ∨ (p4 → p3))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_782422936773951364727562544958 : (((p3 ∨ (((p3 ∨ (((p2 ∨ (p5 → (((False ∨ (p2 → p4)) ∧ (False ∧ p4)) ∧ p1))) → (True ∨ p5)) ∧ p3)) ∨ (p3 → p2)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171824059937441888964083717052 : ((((p3 → (p1 ∨ (p4 → p1))) ∨ (True → (p3 → (p4 ∧ (p3 ∧ True))))) → False) ∨ (True ∧ ((p1 ∧ (p1 → p4)) → ((p5 ∧ p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157355840943122427104040499222 : (((False → ((((((p5 ∨ p1) ∧ (True ∨ p1)) → p5) → False) → (True ∨ True)) ∧ (p5 ∨ True))) → False) ∨ (False → ((False ∧ p1) ∧ (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747020405731785489919508083631 : ((((p4 ∨ p3) → (((p2 → (True ∧ (p4 → (p1 ∧ p3)))) → (False ∨ p3)) ∧ (p3 ∨ (((True ∨ p2) ∧ p5) → (p2 ∨ (p4 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148374071386032942745441473940 : ((((((((True ∨ False) ∧ False) → p2) → False) ∨ (False → (p5 → False))) → False) ∨ ((p5 → p4) ∧ (p5 ∨ p4))) ∨ ((p4 → (p3 ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38342471929808658265381216650 : ((((((p5 ∧ False) ∧ True) ∧ (((True ∧ p3) ∨ ((p1 ∧ (False ∧ p2)) → False)) ∧ p1)) ∧ (True ∧ (((p1 ∧ False) ∧ p3) → p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148423518246908663224442806099 : ((((((p5 → (p5 → True)) → p4) ∨ p4) → ((p2 → (p4 → False)) ∨ True)) → ((p3 ∧ (p4 → p5)) → p4)) ∨ (False → ((p1 → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46833752461837647569287679179 : ((((((p3 → p5) ∧ ((False → p4) ∨ ((False → p5) → ((p1 ∧ True) ∨ p5)))) → ((False ∧ p3) ∧ (p2 ∨ True))) ∧ False) ∨ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229093873811194663299021028683 : ((p5 ∨ (p4 → False)) ∨ (False ∨ (((((False → (p3 ∧ p2)) ∨ p3) ∧ ((p3 ∧ ((False → p5) ∨ False)) → p1)) ∨ p1) → (p3 → (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305310354772279160846266523725 : (p1 ∨ (((p4 ∧ p5) → (p3 ∨ (((p2 ∨ (p4 ∧ p3)) ∧ p5) → ((p1 ∧ (p2 → p3)) → False)))) ∨ (p1 → (p4 → (p5 ∨ (False → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205486841689576857492793227594 : (((False ∧ p5) ∧ ((p2 → False) ∧ p3)) ∨ (((((((False ∧ p3) ∨ False) ∨ p5) ∨ (p5 → p5)) → p1) ∧ ((p2 → (True → True)) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768568331536385884363965447559 : (((p5 ∧ ((((p1 ∨ (False → (True ∧ p4))) ∧ p1) ∧ (((p4 → False) ∨ p5) → True)) ∨ (((p4 → p4) ∨ ((p3 ∧ p5) → False)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113979757764625259166159703883 : (((p1 ∨ ((False ∨ ((((p4 ∨ (p3 ∨ False)) ∧ (p1 ∧ (p2 ∨ (True ∧ p2)))) → p5) → p2)) ∨ False)) ∧ (True ∨ (False → True))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251112250043753622873354721562 : ((p2 → False) ∨ (((((True ∨ True) → p3) → (p4 ∧ ((False ∨ (p3 ∧ (True ∨ (p1 → False)))) → ((p3 ∧ p3) → p5)))) → (p1 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51014546234239988188437176500 : (((False ∧ ((False ∧ p5) ∧ ((p1 → True) → ((p4 ∧ (((True ∨ p3) ∨ False) → p5)) ∧ False)))) ∧ (p5 ∨ (p4 ∨ ((p2 ∨ p2) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116531267512117092296942228907 : (((True ∨ p2) ∧ ((p1 ∨ (p5 → (((((True → p5) ∨ p1) → False) ∧ (p3 ∧ (((True → True) ∨ p5) ∧ p1))) ∨ p1))) → p3)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893385352459300366569834019677 : ((((((p1 ∨ (False → p4)) → (p1 → p2)) ∧ ((p1 → (((True ∨ p3) → p2) ∨ True)) → ((p3 ∧ p1) ∧ True))) ∧ (p5 ∧ (p4 ∨ p2))) → p1) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : (p1 → (((True ∨ p3) → p2) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h15 : (p1 → (((True ∨ p3) → p2) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h15
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68606017751968039458075560138 : ((p4 → ((((p5 ∨ (p4 ∨ p2)) ∨ (((p4 ∨ p3) ∨ (((False ∨ (p4 → p3)) ∨ p3) ∧ ((p1 ∧ False) → p5))) ∧ p5)) → False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41789776769596948107039524878 : (((((p4 → (p5 → p2)) → True) → (p2 ∧ (p3 ∨ ((p5 → p4) ∧ ((p5 ∨ (((p4 → p2) → p2) ∨ (p4 ∧ p5))) ∧ p1))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326946772455174768350226027290 : (True → (((p1 ∨ (((p1 → (((p4 → p1) ∧ (False ∧ (p4 → ((p2 ∧ False) ∨ True)))) → p2)) → p4) ∨ (p1 ∧ False))) ∧ (False → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325689495698004584914702305483 : (p5 ∨ (p1 ∨ (((p1 ∧ False) ∨ (False → (p1 ∧ (p3 ∨ ((True ∨ p2) → (p4 → (False ∧ (p1 ∧ (p3 → p2))))))))) → ((p1 → p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49042003609510457184507105778 : ((((p5 ∨ ((p4 → ((((p5 ∧ p4) → (p3 ∧ ((p4 ∧ True) ∧ p2))) ∧ (p4 ∧ False)) ∧ p1)) ∧ p1)) → p3) ∨ (True ∨ (p3 ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62827377712999447148932341206 : ((p4 ∧ (((p3 ∨ ((False → (False ∧ p3)) ∨ True)) ∧ True) ∧ ((True ∧ (((p4 → p2) ∧ (((p2 ∧ False) ∨ p4) ∧ p3)) ∨ p1)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113428028803231009568303913114 : ((((p3 → ((True → ((((p2 → (p5 ∧ (False → p5))) ∨ (p5 ∧ False)) ∨ p4) ∨ (p2 → False))) ∧ p3)) ∧ True) ∨ (False ∨ p4)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142729224802671665003842079692 : ((p2 ∨ (((p2 → (((p3 ∨ p3) → True) ∧ False)) ∨ ((p4 ∨ p3) ∨ (p2 → True))) ∧ ((False ∧ p4) ∨ (True ∨ p1)))) → (p3 ∨ (True ∧ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- False on the left can always be used.
            apply False.elim h17
          case inr h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- False on the left can always be used.
            apply False.elim h24
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
            case inr h28 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- False on the left can always be used.
          apply False.elim h31
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600369731495279156935528461688 : ((((True ∧ ((((True → (p4 ∨ p5)) → p4) → (((True → (p2 ∧ (p3 → True))) ∨ (p5 ∨ False)) ∧ (p1 ∨ (True → True)))) ∨ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45812061842677411414327003180 : (((p1 → (p5 ∨ (p5 → ((p3 → True) ∧ (((((((p1 ∧ (p5 → (p2 → p1))) → True) ∧ True) ∧ False) → p1) ∨ p2) ∧ p2))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136227474695001959136314950892 : ((((p1 ∨ ((p4 → True) ∧ p3)) → p2) ∨ ((p3 ∨ (((p1 → ((False → p4) ∧ (p3 ∧ p1))) → False) → p2)) ∨ p5)) ∨ ((p3 ∧ p1) → p3)) := by
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
theorem thm_5_vars_150226552216720791975893951781 : ((p2 → (p3 ∨ (p4 ∧ ((p5 → ((p2 ∨ (p4 ∨ p5)) → ((p2 ∧ ((p5 → p4) ∨ p3)) ∨ p5))) ∨ p5)))) ∨ ((p4 → (p5 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148290631560502257593699745360 : (((((p1 ∨ p2) ∨ (False ∧ (((p3 ∨ (p2 ∨ p2)) ∧ p4) ∨ p2))) → (p3 ∧ p3)) → (p5 ∧ (p2 → p4))) ∨ ((p5 → (True ∧ p5)) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312059199507432627366904841410 : (p2 ∨ (p5 ∨ ((True → (p4 ∨ ((((p1 ∨ (p3 ∧ True)) → p4) ∧ ((p2 ∧ True) ∨ ((p2 ∨ (p5 ∧ True)) ∧ p5))) → p3))) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204385437702634046308754846822 : (((True → ((False ∨ p5) ∧ True)) ∧ p1) ∨ ((p1 ∨ ((p2 ∨ True) ∨ p3)) ∨ ((False ∧ ((p4 → (p3 → True)) ∧ p5)) → ((True → p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_311819452816119496971079141245 : (p2 ∨ (p1 ∨ (((p5 ∨ p3) ∧ ((p1 ∧ (p5 ∨ (p3 ∧ p1))) ∧ ((p4 ∧ (True ∧ (True → p5))) ∨ (False → p3)))) ∨ (False → (p1 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102682747569014887988193584930 : (((((((p2 ∨ (((False → p5) ∨ p2) ∧ (p1 ∧ p5))) ∧ (p5 ∧ p1)) ∨ ((p1 ∧ (p5 ∨ p5)) ∨ p3)) ∨ p3) ∨ False) ∨ True) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736402707781297929380768512991 : ((((p1 → True) ∧ (False ∧ (True → (p2 ∧ ((((((p2 ∨ ((p3 ∨ False) → p3)) ∨ p3) ∨ True) ∨ p2) ∨ (p3 ∨ True)) → (True → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47503334668509114772885708959 : (((p1 ∨ (False ∨ (p3 ∧ ((True → (p3 ∨ ((p1 ∧ ((p4 ∨ p2) ∨ p4)) → p2))) ∨ ((p2 ∨ p4) ∧ (p1 → p3)))))) ∨ (p5 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113049157576581563022207598980 : (((p1 ∨ (((p2 → p4) → (False ∧ (True → (p5 ∨ p2)))) → (False ∨ (p3 ∧ (p5 → ((p3 ∧ (p2 ∨ p2)) ∧ p5)))))) → False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66190323735599617480096842189 : ((p5 ∨ ((((((((p2 ∧ False) ∧ False) → ((p1 ∧ p1) → False)) → p5) ∨ True) ∨ p5) → p1) ∧ (((p5 → p1) ∧ (p5 ∧ p5)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711746479162970712832621492200 : (((((((p3 → p1) ∧ p2) ∨ p1) ∧ p4) ∨ ((p3 ∧ (p5 ∨ p1)) ∧ (((((p5 → p1) ∨ False) ∧ p3) ∨ (True ∨ p1)) → (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168777363739900746781643074588 : ((p1 ∨ ((p1 → (False ∧ ((p3 ∨ False) → p4))) → (True ∧ (((True ∨ p1) → p4) ∨ p2)))) → (((True → p5) ∨ (p3 ∨ True)) ∨ (p3 → p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723447444184306224189849909797 : (((((p3 ∧ p4) → p2) ∧ (p3 → ((p2 ∧ p1) ∨ ((True ∧ ((False ∧ (p4 ∧ (((True ∨ p3) → (p1 → p5)) → p1))) ∨ p2)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612682132882481655608668459602 : ((((((((p5 → (p1 → (p1 ∨ ((p2 ∧ p4) ∧ p5)))) ∨ p4) ∨ p2) ∧ ((p4 ∧ (p4 → (False ∨ True))) ∨ p2)) ∨ (False ∧ p1)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_157772197253260179608763859289 : (((((((p1 ∨ False) ∧ p1) ∧ False) ∨ ((True ∧ p5) → p1)) ∧ p5) ∨ ((p2 → (p1 ∧ p2)) ∧ False)) ∨ ((p4 ∨ p5) → (True ∧ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



