variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68510427069925299827994693228 : ((p3 → (p4 ∨ ((p5 ∨ p5) → (((((((p3 ∧ (p1 ∨ (False ∧ False))) ∨ False) ∧ ((p5 ∧ p4) → p3)) → p2) ∧ p2) → p1) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156791059281370248783588120126 : (((p2 ∧ (p5 ∧ ((p4 ∨ (((p4 ∨ (p4 → False)) → p2) ∨ p4)) ∨ ((p1 → p1) ∧ p4)))) ∧ p5) ∨ ((p3 ∨ ((p3 ∨ True) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644704500185312148091842463376 : ((((p1 ∨ (p1 ∨ (p5 → (p1 ∨ ((p5 ∧ (p1 ∨ ((p4 ∨ (True ∨ (p2 ∨ False))) ∧ (((True ∨ p4) → p2) ∧ p1)))) ∧ p4))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190565617551421757309439774466 : (((((p5 ∧ False) → True) ∧ (p4 → (p2 ∧ p3))) → p4) ∨ ((((p2 ∧ ((p3 ∨ (False ∨ p3)) ∧ p3)) ∧ ((False ∨ False) ∧ p1)) ∧ p1) → p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_817377583128267373729700080093 : (((((p4 ∨ ((True → ((p5 ∨ p1) ∧ (p5 ∧ ((False → p4) ∨ (p2 ∨ (False → ((False ∧ p4) ∧ p3))))))) ∨ (p2 → p2))) → False) ∧ p3) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ ((True → ((p5 ∨ p1) ∧ (p5 ∧ ((False → p4) ∨ (p2 ∨ (False → ((False ∧ p4) ∧ p3))))))) ∨ (p2 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689826534315328758563749852024 : (((((p1 → False) ∧ (p5 ∨ ((p2 ∧ (True ∨ p5)) ∧ ((p2 ∨ (False ∨ True)) → p2)))) ∨ (((p2 ∨ (p3 ∨ True)) ∨ (False → p3)) ∨ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114731570489154894890044534734 : ((((p4 → ((p5 ∨ p2) ∧ (True ∧ p1))) ∧ (((True ∧ (p2 → p2)) ∨ True) → p5)) → (p2 ∧ ((p3 → (p4 → False)) → p3))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57867734920941528594232507468 : (((False ∨ (p5 → p3)) → (((((False ∨ p4) ∧ False) → p5) ∧ (p1 ∨ (True ∨ ((True → (p5 → (p1 ∨ p1))) → p3)))) ∧ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684991458102091912895152868664 : ((((p4 ∧ (((True ∧ False) ∨ (p3 → (True ∧ ((p3 ∨ p2) ∧ (p4 ∨ p4))))) → (p1 ∨ False))) ∨ ((p4 ∧ (p4 ∧ (p2 ∨ p3))) → p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137717536319938841838976783124 : ((p1 ∨ (((p4 ∨ p2) → p1) → (((p3 → p2) → (((p1 ∧ p5) → p5) ∧ ((p1 ∨ False) ∧ (p3 → p4)))) ∧ False))) ∨ ((p3 ∨ False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52272937886436706461088825129 : (((False → (p2 ∨ (((True ∧ ((False ∧ ((True ∨ False) ∨ False)) ∧ p1)) ∨ p5) ∨ p5))) → ((False ∨ (p3 ∧ (True → (p4 → False)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228430238604827306834096948210 : ((False ∨ (p5 ∧ False)) ∨ ((p2 ∧ p5) → ((True ∧ ((p2 → p2) ∨ (True ∧ ((p3 ∧ (p3 ∨ p4)) ∨ p1)))) ∧ ((p3 ∨ (p3 ∧ p2)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595135529866199597922261005489 : (((((((p5 ∧ (False ∧ (((p5 ∨ p3) ∨ (p3 ∧ p2)) ∨ True))) ∧ p3) → p3) → (True ∧ (((False ∨ (p5 ∨ p4)) → p5) ∨ p3))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190858382528182892138469503982 : ((((((p4 → p4) ∨ False) ∨ p4) → p5) → (p1 ∧ p4)) ∨ ((p1 ∨ (False → False)) ∨ (p2 ∨ ((p3 ∧ p3) → ((p2 → False) → (p4 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66310621982143989137506280784 : ((p5 ∨ ((False → p3) → (p3 ∧ (False ∨ (((((((p1 ∧ p3) ∧ False) ∧ p5) ∨ p5) ∨ (p1 ∧ False)) ∧ p2) ∧ ((p2 ∧ p5) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51888088659851562468057544480 : (((((p1 ∨ ((p4 ∧ (p3 ∨ ((p5 ∨ p1) → p3))) ∧ True)) → (True ∨ p2)) → p3) ∨ (((p1 → (p5 → p4)) ∧ False) → (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785097003823558381965362749032 : (((p4 ∨ (((((p5 → (False ∧ (p5 ∨ (p3 ∨ p4)))) ∧ p5) ∨ (p4 ∧ ((p3 ∨ p2) ∧ (p4 ∧ (p3 ∨ (p2 ∨ False)))))) → p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657417992366386791012375146790 : (((((p5 → p1) ∧ ((((p1 ∧ (((True ∧ p5) ∨ p4) ∨ ((p1 → p5) ∧ p3))) ∧ True) ∧ p5) ∨ (p1 ∨ (True ∨ p1)))) ∨ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59008484777496469119468118766 : (((p3 ∧ p3) ∨ (((((((p4 ∨ True) ∨ p4) ∨ p5) → (((True ∧ False) ∨ (p1 → p4)) ∨ (p3 → p1))) ∨ True) → False) ∨ (True ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_655097202852841888378617389963 : (((((p1 ∨ (((p4 ∧ (((p2 ∨ (False ∧ (p3 ∧ p3))) → True) → ((False ∨ True) ∨ p1))) ∨ p5) ∨ (p4 → p2))) → p1) ∨ (False ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76757775957484926859819757079 : ((((p1 ∨ (p3 ∧ ((p1 ∨ ((p1 ∨ (True ∧ (p4 → p4))) → p2)) ∧ False))) ∨ (p1 ∨ (((p1 ∨ True) ∨ p3) ∨ (p2 ∨ True)))) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p3 ∧ ((p1 ∨ ((p1 ∨ (True ∧ (p4 → p4))) → p2)) ∧ False))) ∨ (p1 ∨ (((p1 ∨ True) ∨ p3) ∨ (p2 ∨ True)))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43061909966191973903611639669 : ((((((p1 ∨ (p5 ∨ (False → ((p3 → True) ∨ p1)))) ∧ ((p4 ∧ False) ∧ ((p4 ∨ ((True → p2) ∨ p5)) ∨ p5))) → True) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111777649709568605882318592091 : (((((p1 → (True ∧ (p2 ∨ ((((True → True) ∧ p2) ∨ ((p3 ∨ False) ∨ (True → True))) ∨ p3)))) ∧ p5) ∨ (True ∧ p5)) ∨ True) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200256404986227692926719282856 : (((p1 ∧ (p4 ∨ p4)) → ((p2 ∧ True) ∧ p3)) → (p4 → ((p5 ∧ (p2 ∧ p3)) → (p1 ∨ ((p2 ∧ (p2 ∨ ((p2 ∧ True) → p2))) ∨ True))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160973966018738373741019803333 : (((p2 ∨ (p5 → False)) ∧ ((p3 ∨ p5) ∨ ((p5 ∨ (p2 ∧ (p4 ∨ False))) → (p1 ∨ (p1 ∧ p3))))) → (p4 ∨ ((p1 ∧ (p2 ∨ p4)) → p1))) := by
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h32 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h33 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h34 := h24 h33
        -- False on the left can always be used.
        apply False.elim h34
    case inr h35 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h36
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h40 =>
        -- One of the premise coincides with the conclusion.
        exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735817807558875785240333480 : (((False ∧ ((p3 → p3) → p4)) ∨ ((((p4 → (((p3 ∧ ((p5 ∧ (True ∨ p2)) → p3)) ∨ p2) → p5)) ∧ p4) → p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55639171890135433913626353922 : (((((p3 ∧ p2) ∨ True) ∧ True) ∧ (((p2 → p5) ∨ ((p2 → ((True ∧ ((((p5 ∨ p5) → False) ∨ p5) ∧ p5)) → p1)) ∧ p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56549727612130904282166449064 : (((p3 ∨ ((p2 ∨ p1) ∧ p4)) → (((p4 ∨ True) ∧ ((p4 → p1) ∧ p1)) → (((p2 ∧ (p2 ∨ p1)) → ((p5 → p3) ∨ p2)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231659264455204040446158445950 : (((False ∧ p5) → p2) → ((p4 ∧ ((p1 ∧ ((True ∧ (p4 → (p5 → p1))) ∨ True)) → ((p2 ∨ p2) ∨ (p4 ∨ p2)))) ∨ (False ∨ (p2 → True)))) := by
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
theorem thm_5_vars_255212304505098179058192952227 : ((p4 ∧ p4) → ((p1 ∧ (p2 → p2)) → (p3 ∨ (((((p4 → p4) ∨ True) ∧ ((False ∨ True) ∨ p1)) ∧ ((False ∨ True) → (p2 ∧ p5))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255180776766481322227212864958 : ((p4 ∧ p4) → ((((p5 ∨ (((p4 ∨ ((False ∧ p4) ∧ p4)) → ((p3 ∨ ((p1 ∧ p2) ∧ p5)) ∧ True)) ∧ p1)) ∨ p4) ∧ (True ∨ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164562636077089082697931447120 : ((((((p2 ∨ p3) → p3) ∨ p1) ∨ ((True ∨ (p3 ∨ p3)) → ((False ∧ p3) ∧ p2))) ∧ p3) ∨ (((p2 ∧ p3) → p5) ∨ ((p5 ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193756672114306298367235616398 : ((p3 ∧ ((False ∨ True) ∧ (p2 → ((p4 ∨ p1) ∧ p4)))) → (((((p3 → False) → (p2 ∧ (p2 → p2))) ∧ p1) → ((p3 ∧ p2) ∨ False)) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328914587590987438169016000402 : (True → (((True ∨ (((p2 → True) → p4) ∧ True)) → p1) → (p1 ∧ (((p3 ∧ (p1 → p4)) ∧ (((p4 → True) ∨ p2) → False)) → (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (((p2 → True) → p4) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : ((p4 → True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190867181683055898756523588037 : (((((p4 ∧ p5) → p5) ∧ (p3 → p4)) → (p1 → p2)) ∨ (((((p3 ∧ (p4 → (((p3 → p5) → p3) → p4))) ∧ True) ∧ p2) ∧ False) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622771378669977111651376119806 : ((((p4 ∧ (p1 ∨ (p5 ∧ (((p3 ∧ (True ∧ (p2 → True))) → (False ∧ p4)) → ((p2 ∨ p3) → ((p1 ∧ True) ∧ (p1 ∨ p5))))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185210128461475114529040938688 : ((True ∧ (p1 ∨ ((p2 ∧ (True → ((p3 ∨ False) ∨ False))) ∧ p5))) ∨ ((False ∧ ((False → p2) ∨ p4)) → (((True ∧ (p2 ∧ False)) ∨ False) ∨ True))) := by
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
theorem thm_5_vars_217688872436019612874049743435 : ((((p3 → p5) → p1) → True) → (((True → p2) ∧ (((p5 ∧ p3) ∧ p2) ∧ p3)) ∨ ((p1 ∧ p5) ∨ ((p4 → True) ∨ (p5 ∧ (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140074475614352155054387718369 : ((((p1 → False) ∧ (p5 ∨ ((((p4 ∨ p5) → False) ∨ (((p2 → False) ∨ p3) → (p4 ∨ p2))) ∧ p4))) ∨ (True ∨ p3)) → (p3 → (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214782358813101976661996608489 : (((False ∨ p3) ∨ (False ∧ p3)) ∨ ((True ∧ (((((p3 → True) → (p2 → p3)) ∨ p4) ∨ (((p2 ∨ (p4 ∨ False)) → True) ∨ True)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137637854028159280031900081773 : ((False ∨ (((((((False ∨ p4) ∨ (p2 ∧ True)) ∨ (p4 → False)) ∧ p4) ∨ p4) ∨ p3) ∨ ((p3 ∧ (p2 ∧ p2)) ∧ p2))) ∨ (p5 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340859293566035431490736681132 : (p2 → (((((((p3 ∨ ((p5 → True) ∧ ((p4 ∨ p4) → p2))) ∨ p1) → (p3 ∧ False)) ∨ p3) → p5) ∧ ((True ∧ p1) → (p4 ∧ p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134744509821908563274309446189 : ((((p1 ∧ p3) ∨ (False ∨ ((((p1 ∧ True) ∨ (p3 ∨ True)) → ((((p3 ∨ p5) ∨ p3) ∨ p4) ∨ p4)) → p1))) → p2) ∨ ((True ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697982783280663320065507323050 : (((((((False ∧ ((True ∧ p2) ∧ (p1 ∨ p5))) ∨ p3) ∧ p2) ∨ p1) ∨ (((((p3 ∨ False) ∧ p5) → p3) → p1) → (p1 ∧ (False ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776925032371561671685974782168 : (((p1 ∨ ((p4 → (((p3 ∧ p4) → ((p1 ∨ p2) → (((p4 ∨ p1) ∧ False) ∨ (p2 → ((False ∧ False) → (p4 ∧ p4)))))) ∨ p1)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226323856133905529943201997567 : (((p5 ∨ p1) ∨ p3) ∨ (((p3 ∧ (p2 → (p2 → p3))) ∧ p4) ∨ ((p1 → (p3 ∨ (True ∨ (p4 → p1)))) ∨ (((p2 ∨ p3) → p3) ∧ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324706442969443386227915721222 : (p5 ∨ (((True → p5) ∧ p4) → (True → (((False ∧ (((p4 → p3) ∧ True) ∨ p3)) ∧ ((p5 ∨ p3) ∨ (False ∨ ((p2 → p5) → p3)))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399127781288605410585399291639 : ((((p1 → (((p4 ∧ p3) ∨ ((((((True → True) ∨ True) ∨ p5) → p3) ∨ p4) ∧ ((p4 → False) ∧ (p4 → p5)))) ∨ (p4 ∧ p2))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_120823859701642638863278623961 : ((((p1 ∧ (((p5 ∨ (False ∧ (p4 ∧ (p4 ∧ p2)))) → True) ∧ (True → p2))) ∨ ((((True ∧ p2) ∧ p2) ∨ p1) ∨ p5)) ∨ p5) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
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
theorem thm_5_vars_696904514710207005438073065144 : ((((((True → (p2 → (p5 → p2))) ∧ (p4 ∧ False)) ∨ (p4 ∧ p2)) ∧ (p3 → ((((p3 ∧ False) → False) ∨ (p2 ∨ (p4 ∨ p1))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57462800521852711611405540929 : (((True → (p4 ∧ True)) ∨ (((((p5 → False) ∧ (p3 ∨ True)) ∧ ((False ∧ (p2 ∧ p2)) ∧ (p5 → p3))) ∨ p2) ∧ (p1 ∧ (p5 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323991633111806232854309224721 : (p5 ∨ (((True ∧ ((p5 ∨ p4) ∧ ((p3 → p1) ∨ p3))) ∨ (p1 ∧ (p1 → False))) ∨ (p1 ∨ ((False → (p1 ∧ p5)) ∨ (p1 → (p2 ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147115971219922943076510118771 : ((((p4 → p5) ∧ ((p4 → (False ∨ ((False ∨ p4) ∧ True))) ∧ ((False → p2) ∧ (p1 ∧ (p1 ∧ p5))))) ∧ p3) ∨ (((False ∨ True) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716833356470945084576533138328 : ((((False ∧ (p2 → (p4 ∨ p3))) ∧ (((p2 → (False ∧ (p3 ∧ (p4 ∧ p4)))) ∨ (((p4 ∨ False) ∨ p2) ∧ ((p5 ∧ True) ∨ p2))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137116894572891120093555001906 : ((True ∧ ((True → (((p5 → p4) → False) ∧ p3)) ∨ (p3 → ((p5 → False) ∨ (((p5 ∧ (False → True)) ∨ True) → True))))) ∨ ((True ∧ p4) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172340156994265351308714117796 : (((p1 ∧ (True → (p1 ∧ (True → p3)))) ∧ (((p4 ∧ p1) ∧ p2) ∨ (p5 ∧ False))) ∨ (p4 ∨ ((p5 ∧ p1) ∨ (p1 → ((p4 → p1) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42494840857830305654384575558 : (((False ∨ (((p2 ∨ (((p3 → (p5 ∨ p1)) ∨ (False ∨ p3)) → p5)) ∧ ((True ∨ False) ∧ ((False ∧ (p1 ∧ p4)) → True))) → p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40069296904845191442632420240 : (((((p1 ∨ (p4 → (p3 ∨ (p2 ∨ ((((p2 ∨ p1) ∨ (p2 → ((p5 → p3) → p3))) ∨ p1) ∧ (p4 ∧ p4)))))) ∨ p2) ∧ p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245913189339528004478182460877 : ((p3 ∧ p5) ∨ ((((((False → p5) → (p3 → p5)) ∨ p4) → p1) ∨ True) → (p1 → (((p2 ∧ (p4 → ((p4 ∧ False) ∧ p1))) ∨ p3) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187337072122378986481125804087 : ((p2 ∧ (((True ∨ (False → False)) → p4) ∨ ((p3 ∧ False) ∨ p5))) → ((p1 ∧ p5) → ((p2 → p3) ∨ (((p2 ∨ (False → p5)) → False) → False)))) := by
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
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ (False → p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ (False → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328348241534418545586767143774 : (True → (((True ∨ p2) → (p4 ∧ (((p3 ∨ (p4 → p4)) → (p1 → ((False ∨ p3) ∨ (False ∧ True)))) → p5))) → (p3 → ((p1 ∨ p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p3 ∨ (p4 → p4)) → (p1 → ((False ∨ p3) ∨ (False ∧ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h12
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : ((p3 ∨ (p4 → p4)) → (p1 → ((False ∨ p3) ∨ (False ∧ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h21 := h15 h16
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149117338808078130644962165481 : (((False ∧ p1) ∧ (p5 ∧ ((((p2 ∧ ((p1 ∧ ((p5 ∧ p3) ∨ p1)) ∨ (p4 ∨ p4))) ∨ p1) ∧ False) ∨ p1))) ∨ (((p3 → True) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110880577670784142526609648608 : (((((p5 → (p2 ∧ ((((((p2 ∨ False) → p5) → p4) → p1) → p3) → (p5 → p3)))) ∨ (p1 ∨ (p5 ∧ p3))) → p2) ∧ p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588605082045546905228465198609 : (((((True ∧ ((((p1 ∧ (((True ∧ p5) ∨ (p3 ∧ (False ∨ (True → p2)))) → (p3 ∧ True))) ∨ (p3 ∨ p2)) ∨ p5) ∨ p2)) ∨ p1) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41591113507694885515067630076 : ((((p2 ∨ (((False ∧ p5) → True) → (False ∧ p1))) ∧ (p4 → (False → ((p3 ∧ ((p4 ∧ p2) ∨ ((p1 ∧ True) → p3))) → p4)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261289979115392070853576523444 : ((p5 → True) → ((False → p3) → (((((p1 ∨ ((True → p1) ∧ p3)) → True) ∧ (p3 → p1)) ∧ p5) ∨ (False ∨ (True ∨ (p1 → (False ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55043348680247454072512984367 : (((p5 ∧ (p2 ∧ (p5 ∨ (True → p2)))) ∧ ((((False ∧ p2) ∧ (p4 ∧ True)) ∧ ((p4 → p1) ∨ p4)) ∨ (p5 ∧ (p1 → (False ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248889488019824527387381338049 : ((p3 ∨ p5) ∨ (((((p1 ∧ p2) ∧ True) ∨ False) ∨ (True ∨ p1)) ∧ (((p3 → (p1 ∨ (p3 ∨ ((p4 ∧ (False ∧ True)) → p3)))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186479283038834607344793560958 : ((((p2 ∧ (p5 ∧ True)) ∨ (p1 → (False ∧ p5))) ∧ (p2 ∨ p5)) → (((True → p1) ∧ ((p5 → ((p1 ∨ p2) ∨ p5)) → p3)) → (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h21 := h15 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241457411994803364689743669835 : ((False → p2) ∧ ((((False ∧ False) → (p4 → (p2 ∨ p2))) → ((((((p4 → p3) ∧ False) ∨ p3) ∨ False) ∨ (True ∨ (p2 ∨ False))) ∨ p4)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149970107555722485324133145734 : ((p4 ∨ ((((True ∧ p3) → (((p4 → p3) ∨ (p1 ∧ p2)) → (p3 → p1))) ∧ p3) ∨ (True → (True → p5)))) ∨ (((p1 ∧ p2) ∧ p1) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258960154351955663229312301931 : ((True → p3) → ((p2 ∨ ((p2 ∨ (p3 ∨ (((p3 ∧ (((p5 ∨ p1) ∨ True) ∧ (p1 → p3))) ∨ (p3 ∨ p5)) ∨ p5))) ∧ p1)) → (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h21 =>
              -- Disjunctions on the left can always be decomposed.
              cases h21
              case inl h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h17
              case inr h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h17
            case inr h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h17
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h26
            case inr h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h28 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h29 := h1 h28
              -- One of the premise coincides with the conclusion.
              exact h29
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h31 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h32 := h1 h31
          -- One of the premise coincides with the conclusion.
          exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55424454197328968645067555679 : ((((p1 ∨ (p2 → (p2 ∨ p5))) ∨ p4) → ((p3 ∨ (p3 ∨ ((p4 ∧ (((True → True) ∧ p2) ∧ p1)) ∧ p1))) ∨ (p3 ∨ (p5 → p5)))) ∨ p3) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223371724317863783208515826940 : ((True ∨ (p1 ∨ p3)) ∧ ((p4 ∨ (p1 → (p4 ∨ (p1 → p3)))) ∨ ((p1 ∨ (p1 ∨ (((False → p3) ∨ p5) ∨ (p3 ∨ True)))) ∨ (p2 ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615264926518021031420337113308 : (((((p4 → (False ∧ (p5 ∨ ((p1 ∨ (p2 → p5)) ∧ (True ∨ (p5 → (p3 ∧ p3))))))) ∧ ((((p3 → p1) → False) → p2) → p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_48995458063761089512497859195 : ((((False ∨ (((((p4 → (p4 ∧ p2)) ∧ p2) → (p1 ∨ True)) ∧ (p5 ∨ ((False → p3) → p4))) ∨ p4)) ∨ p5) ∨ ((False → p3) ∨ p4)) ∨ p5) := by
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
theorem thm_5_vars_314679500900249569926316836556 : (p3 ∨ (((p4 ∨ (False → (False ∨ (True ∨ ((p2 ∧ (True ∧ (p1 ∧ p1))) → p4))))) → False) → (p5 ∨ ((p5 ∧ p2) ∨ (False ∧ (p4 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (False → (False ∨ (True ∨ ((p2 ∧ (True ∧ (p1 ∧ p1))) → p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691732503453428178679567273665 : ((((p1 ∨ ((((p2 ∧ p1) ∧ p3) ∨ (False ∨ p5)) → ((False → True) ∧ (p4 → p1)))) → (p3 ∨ (((p1 → False) ∧ (p4 ∧ p1)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263569512390516667215829651254 : (True ∧ (((((p1 → (True ∧ p5)) ∧ (p5 ∧ p1)) ∨ p1) ∨ ((p3 ∨ p2) ∨ (p4 ∨ ((p2 ∨ p3) → False)))) ∨ (False → ((p3 ∨ p5) ∨ p5)))) := by
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
theorem thm_5_vars_678294392681528707768760058857 : (((((p2 ∧ (p5 → (True ∧ (p3 ∧ (True ∧ p4))))) ∨ (p4 ∧ (((p1 → p2) → p4) → (True → p1)))) ∨ (((p5 → p2) ∨ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158986835752378707793343670494 : ((p3 ∨ ((p2 ∨ (p5 → p4)) ∧ (((True ∨ (p4 ∧ (((p2 ∨ p4) → p1) ∧ p4))) ∧ p1) ∨ True))) ∨ (p2 ∨ (p1 ∨ (p2 ∨ (p5 ∨ True))))) := by
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
theorem thm_5_vars_38716829983026666874816695247 : (((((False → (p2 ∨ (True → False))) ∧ p4) → ((p1 ∧ ((p2 ∧ p1) ∧ (((p1 → True) ∨ (p1 ∨ p4)) ∨ p3))) ∨ (p4 → p2))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691645488971717625379772735249 : ((((p4 ∧ ((p4 ∨ (p4 ∧ True)) ∨ (p1 ∨ (((False → p5) ∧ p5) → (p4 → True))))) → (p1 ∨ (p1 ∨ (False → (False ∨ (p1 → p4)))))) ∨ p3) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44040642788530293488690266656 : ((((p5 ∧ ((p4 → p2) → (((True → (p2 → p1)) ∧ ((p3 ∨ ((False ∨ True) → (p5 ∨ True))) ∨ p1)) ∨ p5))) → (p1 ∨ True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305304299359547159870260389909 : (p1 ∨ (((((True → p1) ∨ p2) ∨ (p2 → p5)) → ((p2 ∧ (p3 ∧ p5)) → ((p3 ∧ False) ∧ p2))) ∨ ((p2 ∧ False) → (False ∧ (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798225512747002304764210655181 : (((p1 → (((((p4 ∧ ((p5 ∨ p2) ∨ p5)) ∨ p4) ∧ (p2 ∨ (p2 ∧ p4))) ∧ (True → p4)) ∧ (((p2 ∨ (True → p5)) ∧ p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699016200511484323581693614104 : ((((p1 ∨ ((p4 ∨ (((p1 ∨ p1) ∨ p3) ∨ (False ∧ True))) ∧ p3)) ∨ ((False ∧ p4) → (p1 → (True → (False → (True ∧ (p2 ∨ p2))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148509778131430439375697036026 : (((p3 → (p3 → ((p1 → p2) → (p3 → (p2 → (p4 ∧ True)))))) ∨ (((False ∧ False) → p1) → (p5 ∧ p5))) ∨ (p2 ∨ ((p3 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114550596181575625769524283120 : ((((((False → (p3 ∧ p1)) ∧ (p3 → (p1 → (p5 ∧ (False ∧ p2))))) ∧ p4) ∨ True) ∧ (p1 ∨ (((False ∨ p4) ∧ True) ∧ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46317510063399369365841966850 : ((((((((p3 ∧ p1) ∧ ((((p3 → False) ∨ True) → p1) → p5)) ∨ p4) → False) ∨ p3) ∨ ((p4 ∧ (True ∧ p4)) ∧ False)) ∧ (False → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164525704359000539777112916123 : ((((p2 ∧ ((p3 → (p1 → ((p1 ∧ (p3 → p4)) ∨ p2))) → p2)) → (p4 → p1)) ∧ False) ∨ (((p4 → (p5 ∧ p2)) ∨ (p4 ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147490997413412123279841623211 : (((p5 ∧ ((False ∧ False) ∧ (((p1 ∧ p2) → p4) ∨ ((p1 ∨ ((False → p1) ∧ p2)) ∨ (p1 ∨ p5))))) ∨ p5) ∨ (((False → p5) ∨ p5) ∨ p4)) := by
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
theorem thm_5_vars_192883935122030082914659842318 : (((p3 ∧ ((p4 ∧ p4) ∧ (False ∨ p5))) ∧ (p3 ∨ p3)) → ((True ∧ p1) ∨ (p4 ∧ (((p5 ∨ p4) → ((p4 ∧ p1) ∨ (p1 → p4))) ∨ p4)))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346488125405137953210508539151 : (p3 → ((p2 ∧ ((p1 ∧ ((((p5 ∨ (((p2 → True) ∨ (p1 ∧ p5)) → (p3 → p4))) → (True ∨ p3)) → p4) → p1)) → p4)) → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309634924136789387134785191023 : (p2 ∨ ((((p2 ∨ p4) ∨ (p4 ∨ p3)) ∧ (((p4 ∨ (p5 → p2)) ∧ p2) ∧ ((((p5 ∧ False) → True) ∨ p1) ∧ p4))) ∨ (p2 → (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41246954340910353838945146514 : (((((p2 ∧ (((p4 → p1) ∧ (((p2 → True) ∧ p3) ∨ (p3 → p1))) ∧ (p5 ∧ True))) ∨ p1) ∨ ((p5 ∨ (p3 ∧ p2)) ∨ p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791664904227236180217780479755 : (((True → (((True → ((False → (True → True)) → ((True ∨ (False ∧ p5)) → True))) ∧ ((True ∨ (((False ∨ p3) ∧ p1) ∧ p4)) → p3)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190576411993721601970693316951 : ((((False → (p4 → True)) ∨ ((p1 → p3) → p3)) → p4) ∨ (False → ((((p1 ∧ False) → True) → ((p2 → p4) → (p4 ∨ p4))) ∨ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71122432476256701488217833987 : ((((p4 ∧ ((p1 → False) ∧ p5)) ∧ ((p4 → ((p2 ∧ ((p4 ∨ (False ∨ p1)) → p2)) → p3)) ∨ (False ∧ ((p1 ∧ p4) ∨ p3)))) ∧ p1) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112906981232256473550254165773 : ((((p5 ∧ False) ∨ (((((p1 ∧ p4) → p5) → (((p4 ∨ ((p3 ∧ True) ∧ (p1 ∨ p2))) → p5) ∧ p4)) ∧ True) ∨ False)) → False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



