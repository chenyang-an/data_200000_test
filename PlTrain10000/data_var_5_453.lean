variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59165889502532599169093903108 : (((False ∨ p3) ∨ ((True → (p1 → ((p1 ∧ (((False → ((p5 → p3) ∨ p4)) → (p2 → p4)) → (p2 ∨ p2))) → p4))) ∧ (p1 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205381820261179621129982231933 : ((((False → True) ∨ p4) → (p3 ∧ p4)) ∨ ((p2 ∨ ((p1 ∨ p4) → ((False → (p1 → p1)) → False))) → (((p4 ∧ p3) → p4) → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323481702483700106235311509216 : (p5 ∨ ((((p5 → (((False → p2) ∨ (((p1 ∨ (p1 ∧ p3)) → False) ∧ (p5 → p5))) ∨ False)) → (p1 ∨ p4)) → p3) ∨ (False → (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136298308410430996180995873486 : (((p1 → (((p3 → p5) ∨ False) → p4)) → (p3 ∨ ((True ∨ ((((p2 → False) → p5) ∧ p1) → (p2 ∨ True))) ∧ p4))) ∨ ((p3 ∧ p4) → p4)) := by
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
theorem thm_5_vars_158558244203895220919692375235 : ((True ∧ ((((p2 → ((p4 ∧ p3) ∨ p1)) ∨ (((p5 ∧ (True ∨ p2)) ∧ p5) ∧ p4)) → p5) ∨ p3)) ∨ ((p2 ∧ ((p1 ∨ p3) → True)) → p2)) := by
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
theorem thm_5_vars_123905661452750478912678445915 : (((((((True → (False ∨ p4)) ∨ (True ∨ p2)) ∨ p3) → False) ∨ False) ∧ ((p1 → ((p2 ∧ p2) → p3)) → ((True ∧ True) ∨ p3))) → (p5 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((True → (False ∨ p4)) ∨ (True ∨ p2)) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244053571173460222480484308794 : ((True ∧ p2) ∨ (p4 ∨ (p3 → (p4 ∨ (False ∨ ((p2 → False) → (p3 → ((p5 ∨ ((p4 ∨ (p4 → p3)) ∧ (p3 → p1))) ∨ (p5 → p5))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198988212201165675901377584867 : ((p5 → (p2 ∧ (((p4 ∧ p1) ∧ p3) ∧ p1))) ∨ ((p4 ∧ (((((p5 ∨ False) ∧ (p3 → p3)) ∨ ((p1 ∧ p2) ∧ p4)) → p5) → p3)) → p4)) := by
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
theorem thm_5_vars_305133604144463284656459798153 : (p1 ∨ (((p5 ∨ (p4 ∧ (p5 ∧ True))) ∨ ((((p2 ∧ p3) → True) ∧ (((p5 → True) → p1) ∧ False)) ∨ True)) ∧ (p2 → (p2 ∨ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664769249593194529976527865124 : ((((p1 → ((p1 ∨ (((p4 ∨ (p4 ∧ (False → True))) ∨ (p5 ∨ (p1 ∧ (p5 → (p4 ∧ p4))))) ∧ (p1 ∧ p4))) → True)) → (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256394525587087691873201750337 : ((False ∨ p3) → ((((True ∧ ((p1 ∧ ((p4 → True) ∨ ((p2 → (False ∧ False)) → True))) ∨ False)) → (p4 ∨ ((True → p4) ∧ True))) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134186804104429760700941590087 : ((((p2 ∨ ((p5 → ((p5 ∧ False) ∧ (True ∨ (True ∧ p1)))) ∧ False)) ∨ ((((p3 → p5) ∨ True) ∨ p3) ∧ p4)) ∨ True) ∨ (p3 → (p2 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55473970786424037701424100523 : ((((p3 → (False → p5)) ∧ (p4 ∨ p5)) → (p2 ∨ (((p3 ∧ ((p5 ∨ ((True ∨ p3) → p2)) → ((p2 → False) → True))) → False) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330894388019764303282949211440 : (True → (p3 → (p4 → ((((False ∨ (True → p5)) ∧ p2) ∧ ((((((False ∨ (p3 → p5)) → p4) ∨ p4) → (p5 ∧ p5)) → False) ∧ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775333951468371055068622353046 : (((False ∨ (False ∧ (((False ∨ ((p5 → p1) ∧ ((p2 ∧ (p3 ∨ p4)) ∨ ((p3 → p4) → False)))) ∨ p2) ∧ (p1 ∨ ((p3 → p1) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52674789208857528306164376254 : (((p1 ∨ ((p5 ∧ (True → ((p4 ∧ p3) ∨ p1))) → ((p4 → False) → p3))) ∨ ((p5 → p5) ∨ ((((p5 ∨ p5) → p3) ∨ p1) ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731455142165177651578432490737 : ((((True → (False ∨ False)) → (False ∨ (((p4 ∨ ((p2 ∨ p4) ∨ (False → ((p3 ∨ p1) ∨ (True ∨ (p5 ∨ p3)))))) → p5) ∧ (p3 → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140480937632481989586447812961 : ((((((p1 ∧ ((p5 ∧ (False ∧ p5)) → (p4 → (True ∨ False)))) → p2) ∨ True) ∨ True) ∧ (p2 ∨ ((p2 → p3) ∨ True))) → (False ∨ (p5 → True))) := by
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
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48213342119593816451167323164 : ((((p5 ∨ True) → (p3 ∧ ((((p5 → p2) ∧ ((p2 ∨ ((p4 → False) ∧ p1)) ∨ p1)) → p4) ∧ (False ∨ (p4 ∧ p1))))) → (p1 ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133690000335801235682038608039 : (((((p2 → True) ∧ (((p5 → p3) → (p4 ∧ p3)) → (p1 ∨ ((p2 → p3) ∧ p1)))) ∨ ((False ∨ p5) ∨ p4)) ∧ p5) ∨ ((p3 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86504600230806663507450935724 : (((True → ((p1 ∨ (p5 ∧ p1)) → (p5 ∨ (p1 ∨ p3)))) → (p4 ∧ ((p4 ∧ ((p1 ∧ (((p2 ∨ p1) → False) ∧ p3)) ∧ p3)) ∨ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((p1 ∨ (p5 ∧ p1)) → (p5 ∨ (p1 ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : (p2 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37085602219517732963257006279 : ((((((p2 ∧ (((p2 ∧ True) ∨ p4) → False)) ∨ ((((True ∨ True) ∨ False) ∧ (False ∧ p3)) ∧ (p5 ∧ (True → False)))) ∨ p1) ∧ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746613289191514209861563930903 : ((((p3 ∨ False) → ((((False ∧ False) ∨ p4) ∧ ((True → (((p5 ∨ ((p4 ∧ p3) ∨ (False ∧ p5))) ∧ p4) → (p4 ∧ False))) ∨ p4)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137285206867526729374668970990 : ((p2 ∧ ((p2 → (False ∧ (p1 → ((((p3 ∧ (p5 ∨ True)) ∧ p2) ∨ ((p2 → p4) → (p4 ∧ p1))) ∨ False)))) ∧ p5)) ∨ (p1 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82140519173889200318283598495 : (((p2 ∨ (p3 → (p1 ∨ ((((((((p4 ∨ (False ∨ p3)) ∧ True) ∧ p3) → True) → p3) → False) ∨ p3) ∨ p2)))) → ((p4 → p4) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (p3 → (p1 ∨ ((((((((p4 ∨ (False ∨ p3)) ∧ True) ∧ p3) → True) → p3) → False) ∨ p3) ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166108049598130975814142314773 : (((p4 → False) → ((p2 → p5) ∨ (((p1 ∧ False) ∧ p5) ∧ (p3 ∨ (p2 ∧ (p1 → p5)))))) ∨ (p3 ∨ ((((p4 ∨ p4) → True) ∨ p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_302832087456450456058698858391 : (False ∨ (p5 ∨ ((False ∨ (p1 ∨ p2)) → ((p5 → p3) → ((False ∨ False) ∨ ((False ∧ (p2 ∨ p5)) → ((((False ∧ False) → p2) → False) → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2457205179052152919148018497 : (((False ∧ ((p5 ∨ (p2 ∧ p2)) → p2)) ∧ (p4 → p3)) ∨ (p5 → ((((((p3 ∧ p4) → (p3 ∨ p2)) → False) ∧ p5) ∧ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57453639653814838126451710796 : (((p5 ∨ (False ∨ p3)) ∨ ((True → (((False → ((((p1 → False) ∧ p3) ∧ (False ∨ True)) → p2)) ∧ (p2 ∨ False)) → (p3 ∨ p5))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221226156916994641074222907224 : (((p1 ∨ p5) ∨ True) ∧ ((p4 ∧ (p1 ∧ False)) ∨ (((((p5 ∨ True) ∨ (((False ∧ True) ∨ p3) → (p1 ∧ p1))) ∧ False) ∨ (True ∨ False)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_52071997595162214094222267281 : ((((((p2 → p3) ∧ ((p2 ∧ p4) ∧ (p3 ∨ p3))) → ((p5 → p2) → p3)) ∧ p4) → (((p3 ∨ p1) ∧ False) ∧ (p1 ∧ (True → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233224076315147483420934679884 : ((p5 ∧ (p3 → p4)) → ((p5 → ((((p1 ∧ (((((True ∨ p1) → False) → p1) ∧ p5) ∨ True)) ∧ p5) → p5) → (True → False))) → (False ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((p1 ∧ (((((True ∨ p1) → False) → p1) ∧ p5) ∨ True)) ∧ p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h17 := h6 h7
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- False on the left can always be used.
  apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h22 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h23 := h2 h22
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h24 : (((p1 ∧ (((((True ∨ p1) → False) → p1) ∧ p5) ∨ True)) ∧ p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h27
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h34 := h23 h24
  -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
  have h35 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h34, we can now drive its conclusion.
  let h36 := h34 h35
  -- False on the left can always be used.
  apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46151327742226041212226619508 : (((((p4 → (p2 ∧ (p3 ∧ (((p3 ∧ (p3 ∧ p3)) → p5) → (((True ∧ p3) ∧ p5) → True))))) ∧ (p2 → p1)) → p3) ∧ (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793294722229631876400097102221 : (((True → (p3 ∧ (((((p5 ∧ (p4 ∧ p2)) ∨ (True ∧ (((p4 → p4) ∧ (False ∧ p3)) ∧ p1))) ∧ ((p4 → False) ∨ p2)) ∨ p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764102109477421270743215115059 : (((p3 ∧ (p3 → ((((((p1 → True) ∨ (p5 ∧ p5)) → (p2 → p4)) ∧ p2) ∧ (True ∧ p4)) → ((p4 → ((p5 ∨ p3) ∧ p1)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214143587000981371488609649543 : ((((p4 → p5) ∨ True) → p4) ∨ ((p4 ∧ (((p5 → False) ∧ (p4 → True)) → p1)) ∨ ((((True ∨ p5) ∨ (True ∨ True)) ∨ p3) → (False → True)))) := by
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
theorem thm_5_vars_742481470145418921417266654958 : ((((p2 → False) ∨ ((True → (((((p4 ∨ p1) → ((p5 ∧ p2) ∨ p3)) ∧ True) ∧ p4) ∨ (((p3 ∧ (p2 → p4)) ∧ False) → p2))) ∨ p4)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350028231863859931042444811543 : (p4 → ((((((p4 ∧ (p4 ∨ (p3 → False))) ∧ ((p3 ∧ p5) ∨ (p3 ∧ (p5 ∧ (p4 ∧ False))))) → False) ∨ ((p5 ∧ p2) → p1)) → p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261076705004111019574581063945 : ((p4 → p3) → (((((((p5 → p1) ∨ False) → p4) ∨ ((((p5 ∧ True) ∧ (p4 ∨ (True ∧ (False ∨ p4)))) ∨ p4) → True)) ∨ p1) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p5 → p1) ∨ False) → p4) ∨ ((((p5 ∧ True) ∧ (p4 ∨ (True ∧ (False ∨ p4)))) ∨ p4) → True)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674583799388688680546184496976 : ((((True → (p3 ∧ ((p3 ∧ False) ∧ ((((p4 ∨ (p3 ∨ (p2 → (False ∨ p1)))) ∧ False) ∧ p4) ∨ (True ∨ False))))) → (p2 ∧ (p2 → p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64521793362182583573310618950 : ((p1 ∨ (((p5 ∨ (((p5 → p4) ∨ p5) → (False → True))) ∧ p1) ∨ ((p2 ∨ (p4 ∧ (False ∧ (True → (p1 ∨ (p3 → p1)))))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_171731526909496209913431047198 : ((((False → ((p1 → ((p3 → ((p5 → False) → p5)) → True)) ∧ p2)) ∧ p4) → p3) ∨ ((True → p3) ∨ (((p4 → (p1 ∨ False)) ∧ p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_113445902953316353753213805516 : ((((p3 ∧ (p1 ∨ (((True ∨ p1) ∧ p5) → (True → (p3 → (p2 ∨ (((p2 → False) ∧ p3) ∨ p5))))))) ∨ p1) ∨ (True ∧ p5)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191126985476640883241489619779 : (((p2 → (p5 → p1)) ∧ (False ∨ ((p2 ∨ p1) ∧ p2))) ∨ (((p1 ∧ (p4 ∧ True)) ∧ (((p5 ∨ p2) ∧ (p3 → False)) ∨ p1)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263134354667955383299694956282 : (True ∧ ((((p1 ∧ (True ∨ p2)) ∨ True) → (((((p4 ∧ ((p4 ∨ (False → (False ∧ True))) ∨ False)) ∧ p3) → p2) ∨ p1) ∨ True)) ∨ (False ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
theorem thm_5_vars_137676105878965924461827169140 : ((p1 ∨ (((((False → ((((p3 ∧ False) ∧ True) ∧ True) ∧ p3)) → ((False ∧ (p5 ∨ True)) ∧ p4)) ∨ p4) ∧ p5) ∧ p1)) ∨ ((p5 ∧ p4) → p4)) := by
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
theorem thm_5_vars_754625131933054843146659654597 : (((False ∧ (p3 ∧ ((((True → False) ∨ (False ∨ p3)) → (p2 → (False ∧ True))) ∧ ((p2 ∨ p5) ∧ ((((p5 ∧ p1) ∧ True) ∨ True) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118815893665962855971700082108 : ((True → ((p2 ∧ (((p4 ∧ p3) ∧ ((True ∨ (((p3 ∨ p5) → (True → p5)) → (False → p4))) ∧ (p4 ∧ p5))) ∧ p1)) ∨ True)) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780007581844300303350608983315 : (((p2 ∨ ((((True ∨ ((p5 ∨ (p4 ∧ p4)) → p2)) ∨ ((((p1 ∨ (False ∧ p2)) ∨ p4) → p2) ∨ p2)) ∧ (p5 ∨ p1)) ∨ (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249291079661716438606107355926 : ((p4 ∨ p5) ∨ ((((p2 ∧ p5) ∨ (((p5 ∧ (False ∧ p4)) ∨ (p3 ∨ False)) ∨ True)) ∨ (p1 → ((p3 ∧ ((p4 ∧ p2) → p1)) → p1))) ∨ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311892379191168716476489598107 : (p2 ∨ (p2 ∨ (((p1 ∨ (p2 ∨ p2)) ∧ p3) ∨ (True ∨ (p2 ∧ ((p3 ∧ ((((p1 → True) ∧ p4) → p1) ∨ ((p2 ∨ p2) ∨ False))) ∨ False)))))) := by
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
theorem thm_5_vars_613705599873524028392489789682 : (((((((False ∨ p5) ∨ p2) ∨ ((True → (p5 → (True ∨ p5))) ∧ (((False → p2) ∨ p3) ∧ (p1 → p1)))) ∧ (p4 ∨ (p1 ∨ True))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172219856498929859209451945401 : (((True ∨ ((p5 → p4) ∨ ((False ∨ (False ∨ p5)) ∧ p3))) → (p2 ∨ (p3 → p1))) ∨ ((p2 → (p2 ∧ ((p4 ∨ p2) → False))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186658285404788678533277858753 : ((((((True → p1) ∧ False) → p1) → p2) ∧ (False → (True ∨ p2))) → (p2 → (((p2 → False) ∧ (p4 → (True → (p2 → p5)))) → (p4 ∨ False)))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658256123311385640852707346086 : ((((p5 ∧ (p1 ∨ ((p4 ∧ ((((p1 ∧ p3) ∧ p5) → True) ∧ p3)) ∧ ((p5 → (True ∨ False)) → (p2 ∨ (p5 ∧ p5)))))) ∨ (True ∨ p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_699880263131341916805345481471 : (((((((p3 ∨ (p3 → True)) → p4) ∧ p1) ∨ ((p5 ∨ True) ∧ p4)) → (((p3 ∧ p4) ∧ (p2 ∧ p2)) → (((p2 → True) → p5) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44982779224346964471284668134 : ((((p3 → p1) ∧ (p4 ∨ (((True ∨ True) ∨ (((((False → (((p2 → p1) ∨ p1) → p4)) → p5) ∨ p4) ∧ False) ∧ p4)) ∨ p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353442831869872782249500946406 : (p4 → (p1 ∨ ((False → (p3 ∧ p4)) → ((p3 → (p1 → ((True → False) → (False → p2)))) → ((p1 ∨ p5) → (((p3 ∨ p4) ∨ p1) ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631286792317260425771354166916 : (((((((p3 → p5) ∨ ((p1 ∨ (((((p5 ∨ (p1 ∧ p4)) ∨ p1) ∧ False) ∨ ((p2 ∧ p2) ∧ p2)) ∨ p2)) ∧ True)) → p2) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33165546538796943033164265927 : ((p3 ∨ (p3 ∨ (((True ∨ p2) → ((p3 ∨ (p1 ∧ (False → p2))) ∨ ((((False → p4) → (p2 ∨ p5)) → p3) → True))) ∨ (p5 ∧ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159054191305918619970442186284 : ((p5 ∨ ((p3 ∨ (False ∨ ((p1 → p4) ∨ ((False ∧ p2) ∨ (p3 ∨ False))))) ∧ ((p1 ∨ p5) ∧ False))) ∨ (True ∨ ((p5 → p3) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242550558183024921773467022013 : ((p3 → True) ∧ (((p3 ∨ (((p4 ∧ p3) → p5) ∨ p4)) → ((False ∨ p2) ∨ ((((p5 ∨ p5) ∨ (p4 → p4)) ∨ p4) ∨ (p3 ∧ True)))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115022766449445824062116648275 : (((p1 ∨ ((p2 ∧ (p2 → ((p3 ∨ p1) ∨ p5))) → (p4 → True))) ∧ (p2 ∧ (p4 ∧ ((p3 ∨ ((p3 ∨ p4) ∧ p2)) ∧ p4)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136275310079279762895067368448 : ((((p5 → (p5 ∧ p4)) ∧ (p4 ∨ p4)) → ((True → (True → p3)) ∧ ((True → (p3 → False)) ∨ (p2 ∧ (False → p4))))) ∨ ((False ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62379628766458611422600881529 : ((p3 ∧ (((p3 → p3) ∧ (((p1 ∧ (p3 ∨ (False → p2))) ∨ (True → p1)) ∨ False)) ∨ ((p1 ∨ p1) ∧ (((True ∧ p2) ∨ True) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136456471346370334300991158502 : (((p5 ∨ (False ∧ (p1 → p1))) → (((((p3 ∨ (True ∧ (p1 ∨ (p1 ∨ p4)))) → p1) ∨ p2) → p2) ∧ (p4 ∨ True))) ∨ (True ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45366978434418203925188193328 : (((p4 ∧ (((True ∨ p5) ∨ p4) ∧ (((False ∨ p5) → p4) → ((p5 → True) ∧ ((p2 → (p4 → (True ∧ (True ∧ p2)))) ∧ p5))))) → p5) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((False ∨ p5) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h8
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : ((False ∨ p5) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h21 := h5 h17
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51866152432573971285930688303 : (((((((p3 → p5) ∨ p5) ∨ (p4 ∨ (p4 ∨ p5))) ∧ ((p4 ∧ p3) ∨ False)) ∨ True) ∨ (((False ∨ False) → p1) ∨ (p5 → (False ∧ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152530553649465571481217867341 : ((((p3 ∧ False) ∧ p4) → ((p1 ∨ ((p1 ∨ ((p5 → p1) ∨ (((p3 ∨ p5) ∨ p1) → True))) ∨ False)) → p3)) → (True ∧ ((p4 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14643088000442236090345968420 : (((((p4 ∨ p1) ∧ ((p5 → ((((p1 ∨ ((p3 → True) ∨ p5)) ∨ p3) ∧ (p1 ∧ True)) ∨ p4)) ∨ (p2 → p4))) → p2) ∨ (True ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67780701173741275997787560180 : ((p2 → ((p3 ∨ (p2 ∧ (p3 → (((p2 → p4) → ((p2 → ((p3 → False) ∨ p2)) ∧ (True → p3))) → (False ∨ (p2 → False)))))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224948313100598021311040230889 : ((p5 → (p2 → True)) ∧ ((p5 → (((p2 ∨ p5) ∨ p3) → ((((False → p1) ∨ p3) → (True ∧ (p2 ∧ p2))) ∨ (True ∧ (p1 ∨ p3))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651768828014016807393460836486 : (((((p3 → False) ∨ ((p5 ∧ (p2 → ((p1 ∨ ((p2 → p2) ∨ (p4 ∨ p4))) ∨ ((p2 ∨ False) ∨ False)))) → (p4 ∨ p2))) ∧ (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200263633427290265688437954531 : (((p5 ∧ (True → True)) → ((p3 ∧ False) ∧ p5)) → (p5 → (((p1 ∨ ((((p2 ∧ p5) ∧ True) ∧ (False ∨ p1)) ∧ p1)) ∨ (False → p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312413006428633978884848733186 : (p2 ∨ (p4 → (((p4 ∨ p4) ∧ (p1 ∨ (p4 → (((((p5 ∨ (True ∨ p1)) ∧ (p1 ∧ True)) → p1) → p5) ∧ ((True → p5) → False))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136461722583488326765246265620 : (((p3 → (p4 ∧ (p2 → True))) → (p5 ∨ ((p3 ∧ p4) ∧ ((False ∨ ((True → (p3 ∨ False)) → p4)) → (False ∨ True))))) ∨ (p5 ∨ (True ∧ True))) := by
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
theorem thm_5_vars_158505469930319033210325725317 : (((True ∨ p3) → ((((((p3 → False) ∨ p3) ∧ p4) ∧ p2) ∧ ((p1 ∨ p5) ∧ p3)) ∧ (p4 → p4))) ∨ ((((False → p5) → True) ∧ False) → p4)) := by
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
theorem thm_5_vars_467515727389022015751059543636 : ((((((p5 ∨ (p1 ∨ ((p5 ∧ False) → p4))) → p2) ∧ (p3 ∧ (p1 ∧ p4))) ∨ ((p2 → (p2 ∧ (False → (p3 ∧ (p4 ∧ True))))) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357384999208232002200067513569 : (p5 → ((p3 ∧ True) → (((((True ∧ False) ∧ p2) → (p1 ∨ p5)) → ((p1 ∨ ((p4 → False) ∨ False)) ∨ (True → p5))) ∧ (p2 → (p5 → True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118733087164475760684695813566 : ((p5 ∨ ((p4 ∨ (((p1 ∧ (p4 ∨ (((p1 → p5) → p3) ∧ False))) ∧ False) → p2)) → (p2 ∨ ((True → True) ∨ (False ∨ p4))))) ∨ (p1 ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781905846679517323972120595375 : (((p2 ∨ (p2 → ((p4 ∧ ((p4 ∧ True) ∨ (((p2 ∧ ((p5 → ((p1 ∧ True) ∧ p5)) → (False ∨ p3))) ∧ p5) ∨ (p2 → True)))) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214633912967960179071843405697 : (((p1 → True) ∧ (p1 → p3)) ∨ (((p5 → (p2 ∧ False)) ∨ True) → (((p4 ∨ p1) → p5) ∨ (False → (((p2 ∨ p4) → (p1 ∧ p2)) ∨ False))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41924645799147868214868287151 : ((((p5 ∧ (p1 → p5)) → ((p4 ∧ ((((p2 ∧ (p2 ∨ p4)) ∧ False) ∨ p2) → (p1 → (((p1 → p3) → p3) ∧ p4)))) ∨ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792753197287414211466585246972 : (((True → (((p2 ∨ p1) ∧ (True → p5)) → (((p4 → ((((True → p1) ∨ True) ∧ p4) ∨ p2)) ∨ p1) → ((p2 → (False ∨ p3)) ∨ p5)))) ∨ p4) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h21 := h15 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354634495209963096990844414964 : (p5 → (((p2 → ((False → ((((False ∨ p4) ∨ (p2 ∨ ((p5 ∧ True) ∧ (False ∧ p5)))) ∧ (p5 ∨ False)) → p2)) → (p5 → p4))) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187688880362723507370040546381 : ((False → ((p3 ∧ (((p3 ∨ p5) ∧ (p2 → p3)) → True)) ∨ False)) → (((True → p1) ∨ p1) ∨ (p1 → (((p1 ∧ p5) ∧ (p1 ∧ False)) ∨ True)))) := by
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
theorem thm_5_vars_321304435341923299405345800624 : (p4 ∨ (p5 ∨ ((((p2 ∧ (p4 → p5)) ∧ (p3 → ((False ∧ ((p2 ∨ True) → (False ∨ p3))) ∨ p2))) ∧ ((p3 ∧ p5) → p1)) ∨ (False → p1)))) := by
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
theorem thm_5_vars_118424706327216867833244594001 : ((p2 ∨ (p1 ∨ (p2 ∨ (((p3 → (p2 ∨ p5)) ∨ (p5 ∧ (p3 ∨ ((p1 → (False → p2)) ∧ ((p3 → p1) ∨ p5))))) ∨ False)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224300951944410924576779171477 : ((False → (p5 ∧ p5)) ∧ ((((((False → (((p2 → True) ∨ (p4 ∧ p4)) ∨ False)) → ((p2 ∧ p2) → p1)) → p3) ∨ p5) → False) ∨ (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46903068003012081935272324998 : ((((((p5 ∨ ((((p2 ∧ p2) → (False ∧ (p4 → False))) ∧ (p2 ∧ p4)) → (True ∨ p4))) ∧ p2) → (p4 ∨ p1)) ∨ True) ∨ (p4 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259027974077611364475768295112 : ((True → p4) → (((False ∨ False) ∧ ((((p5 ∨ (p1 → p2)) ∨ p4) ∨ p1) → (p1 ∧ False))) ∨ ((False ∧ (p5 → p1)) → ((p1 ∧ p3) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153062065238733365890895699693 : ((p3 ∧ (((p1 → True) → ((p3 ∨ ((p3 → (True ∧ p5)) ∨ ((p5 ∧ p4) → p5))) ∧ (p5 ∨ p1))) → p5)) → ((p3 → p5) ∨ (p1 → True))) := by
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
theorem thm_5_vars_264795799910250070410607593921 : (True ∧ ((p1 ∧ False) ∨ ((p3 ∨ p2) → ((p3 → ((((p4 ∧ False) ∨ True) → p4) → ((p5 ∨ p4) ∧ p3))) ∨ (p5 ∧ ((False → p1) ∧ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207378176647037481292456787729 : (((True ∧ (p5 → (p3 ∨ p1))) ∨ p5) → (((((p1 ∨ (p1 → False)) → True) ∧ (p2 ∨ True)) ∨ True) → (p1 → (p4 ∨ (True ∧ (p2 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      cases h1
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60893293940060862592211722994 : ((True ∧ (p3 → (p5 ∨ ((((p3 → p1) ∨ True) ∧ p3) → (p1 → ((p5 ∨ (p5 ∧ p3)) ∨ (((False → p2) ∨ p5) → (True → p1)))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148610152469640652963067603082 : (((((True ∨ ((p5 → False) ∨ (p5 ∧ True))) → p2) ∨ p1) → (p2 ∧ (((p3 ∨ p4) → p3) → (p4 ∧ p4)))) ∨ (p5 → (True ∨ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117883530087689049192890229654 : ((p5 ∧ ((p3 ∨ (True ∨ ((p2 ∨ True) → (((p3 ∨ ((True ∧ p5) ∨ p2)) → ((p3 ∨ p2) ∧ True)) → (p1 → p3))))) → p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309352342504344579397725950627 : (p2 ∨ (((((((p3 ∧ p3) ∧ (p3 → True)) ∧ p1) ∧ (True → p5)) ∨ p5) → ((p1 ∧ (False → p5)) → (p4 ∨ (p3 ∧ p2)))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148204353426668484161961165547 : (((p4 ∧ ((p3 ∧ ((((p4 ∨ p2) ∨ ((p4 ∧ False) ∨ p4)) → p2) ∧ p5)) ∧ True)) ∧ (False ∨ (True ∨ p4))) ∨ (((p1 ∨ p4) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211236076860991096808333544956 : (((False ∧ p4) ∨ (False → True)) ∧ (((((False ∧ (((p4 ∨ (((p2 ∧ p4) ∨ p2) → p1)) ∨ p5) ∨ False)) ∧ p5) ∨ False) ∨ (True ∨ p3)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



