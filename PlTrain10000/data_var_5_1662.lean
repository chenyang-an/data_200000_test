variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187537968294469680732553340632 : ((p2 ∨ ((((p5 ∧ p5) ∧ True) ∧ (p1 → (p4 ∧ p2))) ∨ p4)) → (((((p3 ∧ False) ∨ ((p5 ∧ p5) ∧ (p3 ∨ p2))) ∧ p2) ∧ False) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
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
theorem thm_5_vars_343519398662107992743112434043 : (p2 → ((p3 ∧ p3) → (p3 ∧ (((p5 ∨ (p5 ∧ p5)) ∨ ((((p3 ∧ False) → (p5 ∧ False)) → (p1 ∨ ((p3 → False) ∨ p2))) ∨ p1)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122664373744253420892856080083 : (((((((p4 → p3) ∧ p3) → (p2 ∨ (p1 → (p2 ∧ p2)))) → (p4 → p4)) ∨ (True → ((p2 → p3) ∧ p2))) → (True ∧ True)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919842338038953433327837124014 : ((((True → (((p5 → (False ∨ (p5 → False))) ∧ ((False ∧ True) ∧ p2)) ∧ p3)) ∧ ((p1 ∨ ((False ∨ p2) → ((True ∧ p5) ∨ p4))) ∧ p3)) → p5) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_984273940778742999110636503285 : (((p1 ∧ (False ∨ ((((False ∧ False) ∧ ((p1 ∨ p3) → p5)) ∨ ((True → (p1 ∧ ((p4 ∧ p2) ∨ (p1 ∧ p4)))) ∧ (p3 → p5))) ∨ False))) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685459201180575729522119382038 : ((((((p3 ∧ (p4 → ((True ∧ ((p4 ∨ True) ∨ p4)) ∧ p2))) ∨ ((p5 → False) → p4)) ∧ p4) → (((p3 ∧ p5) ∧ (p2 ∧ False)) ∨ p4)) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64797034519393007216600499366 : ((p2 ∨ (((p5 ∧ p5) ∨ ((p2 ∨ ((p4 → (p2 ∧ p1)) ∨ ((p3 ∧ p1) ∨ ((False → p1) ∨ p3)))) → ((p5 → p5) → p3))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160812853428740700030537293950 : (((((p5 → False) ∨ (p4 ∨ p2)) ∧ p3) → (False ∨ (((p2 ∨ (p4 ∨ True)) → (p5 → p1)) ∧ False))) → ((p3 ∨ ((p4 ∨ p1) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65555936228135423116929222439 : ((p3 ∨ (p1 → (((p2 ∨ (False ∨ p1)) ∨ ((p1 → p4) ∨ (p3 ∧ p2))) ∧ (((p4 ∨ p2) ∨ (p2 ∧ (False → (p5 → p2)))) ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136924835169394928204423726472 : (((p1 → p5) ∨ ((p2 ∧ p2) ∨ ((True ∧ p1) ∨ (p5 → ((p2 ∨ p5) ∧ ((((p3 ∧ p4) ∧ p2) ∧ p5) ∨ p4)))))) ∨ ((True ∨ p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165773197867882517471867114028 : ((((False ∨ (p3 → p3)) → p5) → ((True ∧ (((p5 ∨ p3) ∨ (True → True)) → p4)) ∨ p3)) ∨ ((True ∨ ((p2 ∨ p2) ∧ p2)) ∨ (p2 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670319528924062984569527961225 : (((((p5 ∧ (p2 → p5)) ∧ (((p1 → (p5 ∧ True)) ∧ p3) ∨ ((((p1 → p1) ∨ (False ∨ p3)) → p2) ∧ True))) ∨ (p1 ∧ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178094878136799561662663296994 : ((((p5 ∨ (p4 ∨ (False ∧ ((p2 → p1) ∨ (p3 ∨ p4))))) → True) → p3) ∨ (((((p5 ∧ True) ∨ p4) → (p2 ∨ p1)) → p3) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119533777939190333784615936636 : ((p5 → ((((p5 ∧ p1) ∨ p1) ∨ (False → (p5 ∧ ((p2 ∧ (((p5 ∧ p3) ∨ True) ∨ p1)) ∧ ((p5 ∨ p2) → False))))) → p3)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44333564921700675460901840548 : (((((((False ∨ (p5 → False)) → (p4 ∨ ((p5 ∨ p3) ∧ p1))) ∨ (False ∧ False)) ∨ False) → (((p5 ∧ p4) ∨ (p2 ∨ p4)) ∧ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256625821869253778989232084603 : ((p1 ∨ True) → (True → (((((p5 → (p4 ∨ False)) → (True ∧ (p1 ∨ p5))) → p5) ∨ p1) ∨ ((p1 ∨ True) ∨ ((False → (p1 → p1)) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166071327374373662969135249204 : (((True ∨ p3) → (p5 ∨ ((((p1 ∧ ((True ∧ (True ∨ p1)) → True)) ∨ p3) → p1) ∧ p2))) ∨ (False → (True ∧ (p5 → ((p1 ∨ False) → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191792368162572435882461013307 : ((p2 ∨ ((((True ∧ p1) ∨ True) ∨ (p3 ∨ p5)) ∧ False)) ∨ (p5 ∨ ((p4 ∨ (p5 → (False ∧ False))) → ((((p2 → p3) ∧ p2) → p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738957324907574513251362058585 : ((((p3 ∧ p1) ∨ ((p3 ∧ p1) ∧ (True → ((False → (p1 ∧ ((p2 → (p5 → p3)) → (((p4 ∨ (p3 → p5)) ∨ False) ∨ False)))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777051395700820099621235148605 : (((p1 ∨ (((((p1 ∧ p4) ∧ p2) → (p1 → p2)) → (((p3 → ((p4 → (p2 ∨ (p1 ∧ p4))) ∨ p3)) ∨ p5) ∨ p4)) ∨ (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790326100063300679590078490445 : (((p5 ∨ (p3 ∧ ((((False → p3) ∧ ((True → (((p5 → (p3 ∨ (p2 ∧ True))) ∨ (p4 → p4)) ∨ p1)) ∧ p5)) → p4) ∧ (p4 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147431388135425250821077662857 : (((((p3 ∨ True) → True) → (((p3 ∧ p4) ∨ (((p1 ∨ p2) ∧ (True ∨ (p1 → True))) ∧ False)) ∧ p2)) ∨ False) ∨ ((p5 → p1) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191807773557407078963936277368 : ((p2 ∨ (((p3 → p1) ∧ True) → (p1 ∨ (False ∨ False)))) ∨ (True ∨ (((p4 ∧ p4) → (p4 → ((p5 ∨ ((p1 ∨ p3) ∧ p5)) ∨ False))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803032997919094383313409504527 : (((p3 → (((((((p1 ∨ p1) ∨ p5) ∨ False) → p4) → p3) → (p4 ∨ ((p4 → (p5 ∨ False)) → ((True → (p1 ∧ p3)) → p5)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148124016270528616643484684002 : ((((p2 → (p3 → False)) ∧ (p5 ∨ (((p3 → p5) ∧ ((True ∧ p2) ∨ p3)) ∨ (False → False)))) → (p1 ∧ p4)) ∨ (True ∨ (p1 → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55871937488194940201736641344 : (((True ∨ ((True → True) ∨ p1)) ∧ (((p5 ∧ ((p2 ∨ p1) ∧ ((False → p1) ∨ p3))) → ((p5 → False) ∨ (False → p3))) ∧ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323096532220964190464282235685 : (p5 ∨ (((False ∧ ((p1 ∧ (p3 → (p3 ∧ ((p3 ∧ (p1 ∧ p5)) ∨ (p2 → p4))))) ∨ p3)) ∨ ((True ∨ p4) ∨ (p5 → p4))) ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199931550021138342596235103972 : ((((p4 ∨ p2) → (p5 ∨ False)) ∨ (p1 ∧ p4)) → ((p2 ∨ (True → (((False ∨ p5) ∨ True) ∧ (p1 → (p1 ∨ p2))))) ∨ (p5 → (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37434335839084892391884090217 : ((((((p2 ∧ (((p4 ∧ p1) ∧ p2) ∧ p3)) ∧ (p2 → (((p1 ∨ p3) ∧ p5) ∧ p1))) ∧ ((p4 ∨ p4) ∧ (p1 ∨ p5))) ∨ True) ∧ True) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482451549659379514933210351363 : ((((((p3 → p5) ∨ (False ∧ p1)) → (True ∨ True)) → ((((True ∧ (p5 → (p1 ∨ (p2 → p5)))) ∨ (p1 → p3)) → (p1 ∨ p5)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215335987258688715322707938092 : ((p1 ∧ (p4 ∨ (True → p4))) ∨ ((((((True ∨ p3) ∨ (p4 ∨ p5)) → ((p3 ∨ p3) ∨ False)) ∨ p3) → True) → (((False ∨ p3) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345450165703751346606883513110 : (p3 → (((p2 ∨ ((p4 ∧ ((p4 ∨ p3) ∧ p1)) ∧ (True ∧ ((p5 ∨ p1) ∧ (((p2 ∧ p5) ∧ p2) ∨ (p1 ∨ p1)))))) ∨ (False ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350305155182965597258952278782 : (p4 → ((p3 ∨ (((False ∨ ((((p1 ∧ p1) → False) → (p2 ∨ p3)) ∧ True)) ∨ (True → ((p1 ∧ (False ∧ p2)) ∧ p1))) ∧ (p1 ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168098786790307824234657062259 : ((((p4 ∧ p1) ∧ (False ∧ p4)) ∨ (True ∨ (((p5 → p1) ∨ (p1 ∨ True)) ∧ (False → False)))) → ((p3 ∨ p2) ∨ (p5 → (p5 ∨ (p5 → True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134529015836025960396943243653 : (((((((p1 ∨ (p4 → ((True → p1) ∨ True))) ∧ (p2 ∧ p2)) → (((p3 ∧ p4) → False) → False)) ∨ p4) → p3) → p3) ∨ (p5 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204098307229809882828848285096 : ((p5 → (p2 → ((False ∧ p2) → False))) ∧ (((p5 → (p2 ∨ (p5 → p2))) → (((p1 ∨ p2) ∧ (p5 ∧ ((p5 ∨ p4) → True))) ∧ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156900626549969876130497090263 : ((((p4 ∨ ((True ∧ (p5 ∧ p2)) → (((p5 → ((p4 ∧ p1) ∧ p5)) → False) ∧ p4))) ∨ p5) ∨ True) ∨ ((True → p2) ∧ (p5 ∧ (p1 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215915967648551704546626899516 : ((p3 ∨ (p2 ∧ (False ∧ p2))) ∨ ((((p2 → ((p3 → (True ∨ False)) ∧ True)) ∧ p4) ∨ (p3 → (True ∧ (p4 → ((p1 → p5) ∨ True))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314258738299869739810052649089 : (p3 ∨ ((((True → p3) ∨ (p3 ∨ False)) ∨ (((p2 ∨ ((((p3 → (False → p1)) ∨ p1) ∨ True) ∨ False)) → p5) → p1)) ∨ (False → (False ∧ p2)))) := by
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
theorem thm_5_vars_178623270630470115201350397022 : ((((((p4 → p5) → p5) ∧ False) → p1) → (p1 ∧ (p2 ∨ (p5 → p3)))) ∨ (p5 ∨ (((p3 ∧ p2) ∨ ((False ∨ (p5 → p5)) ∨ p3)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254913208569746553834141644396 : ((p4 ∧ True) → ((p5 ∨ p3) → (((((p5 ∧ ((p5 ∧ p5) → p1)) ∧ (False ∧ p3)) ∨ (p3 ∨ (p2 ∧ (p3 ∨ (p2 ∧ p5))))) ∨ p4) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147527619859635078695468019154 : (((True → (p2 ∨ ((p5 ∨ p1) ∨ ((False ∧ p1) ∧ (True → ((p5 ∨ (p3 ∨ (p5 → p4))) ∧ p5)))))) ∨ p4) ∨ (p1 ∨ (False → (True ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62381143217840111301559471087 : ((p3 ∧ ((((((p3 ∨ (False → p2)) → (False ∧ (p1 ∨ p5))) ∧ p4) ∨ p2) ∨ p1) → ((((p1 ∨ (p1 → p1)) → p4) ∨ p4) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305303741471974710442899235645 : (p1 ∨ ((((((p3 ∨ p4) ∨ p2) ∨ p3) ∨ True) ∨ ((p5 ∨ ((p1 → (p1 → p2)) → p3)) ∨ False)) ∨ ((p1 ∨ (p3 ∨ p3)) → (p2 ∨ p1)))) := by
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
theorem thm_5_vars_323498036870136468944842367983 : (p5 ∨ ((((False ∧ p2) → (((p5 ∧ (p1 → (True ∧ p3))) ∧ p1) ∨ p5)) → ((p4 → ((False ∧ True) → p1)) → p3)) ∨ ((p2 ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55123151260315801487880988823 : (((((False → p1) ∨ (False ∨ p3)) ∧ p3) ∨ (((p5 ∧ ((p3 ∧ (False → p5)) ∨ (p4 ∧ (p2 ∨ ((p3 ∧ False) → p1))))) → p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225996594646198016947194826726 : (((p4 ∧ True) ∨ p2) ∨ (((p3 ∧ (p2 ∨ p2)) ∨ (p2 → (p1 → ((False → (((p4 ∧ (p5 ∧ p2)) ∧ True) ∧ p5)) → (p2 ∨ p2))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178131857696779345406578152016 : ((((((True → True) → False) → p3) ∧ (p4 → ((p5 ∨ p1) → True))) → p1) ∨ ((False → p2) ∧ (p4 → (((p4 ∨ p2) ∨ p5) ∧ (p4 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342154648746818933669058087445 : (p2 → (((((True → (True ∨ (p3 → p3))) → (p3 ∨ p1)) → ((True → (p5 → p2)) → False)) → (p5 ∧ p5)) ∨ ((p5 → (p2 → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259856240954015695383544838115 : ((p1 → p4) → ((((p1 ∨ p4) ∨ ((((p1 → (((p2 ∨ p3) → p4) ∨ p5)) ∨ p5) → p1) ∧ (((True ∨ p1) ∨ p1) ∨ p1))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61058746758440938885252984508 : ((False ∧ ((((((p1 ∧ p4) → ((p2 → (p3 ∧ False)) ∧ True)) ∨ (True ∧ p5)) ∧ p1) → ((False → p2) → p5)) ∧ ((True → True) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134173362482251806019572809175 : (((((((((p4 → (p1 ∨ False)) → (p2 ∨ p2)) ∨ p3) ∨ p1) ∨ p3) ∧ p5) → ((p2 → False) → (p1 → p3))) ∨ p3) ∨ (False → (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308484744777996197718713779728 : (p2 ∨ (((((p1 ∧ ((p2 → False) ∧ ((False ∧ ((((False ∧ p4) ∧ p1) → p2) ∧ p2)) → p3))) → p4) ∧ p2) ∨ ((p5 → p5) ∨ p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_148402278781174771608532429833 : (((p2 → ((True ∨ p2) → (p1 → (((p2 ∧ p4) → (p2 ∨ p5)) → p5)))) ∨ (p1 → (p3 ∧ (False ∨ True)))) ∨ ((p2 → p5) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206279734768491115959655943109 : ((False ∨ (p3 ∨ (p3 ∧ (p3 ∨ p2)))) ∨ (((((p2 ∨ False) ∧ True) ∨ ((p4 ∨ True) → p2)) ∨ (p3 ∧ ((True → p4) ∨ (p1 ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252641374763998818714008269475 : ((p5 → p4) ∨ ((((p4 ∧ (((p5 → (p4 → (p5 → p3))) → ((p3 ∨ False) ∧ p3)) ∨ ((p3 ∧ False) ∨ False))) ∨ p4) ∧ False) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258958264557292148332473091873 : ((True → p3) → (((p4 ∨ p3) ∧ (((True ∧ ((((((p2 ∨ False) ∧ p2) → True) ∨ (p1 ∧ p2)) ∧ p4) ∧ p2)) → p5) → p3)) ∨ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661983325403473711642003891437 : (((((((((p1 → (True ∨ False)) ∨ False) ∨ True) ∨ (p2 ∨ (p1 ∨ p4))) ∧ False) → (p4 ∨ (((p4 ∧ p5) ∧ p2) → p1))) → (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66378764739837225947647197640 : ((p5 ∨ (p3 ∨ ((p2 ∨ (p5 ∨ p4)) ∨ ((p5 ∧ (False → p3)) → (False ∧ (p1 → (((p4 ∨ p3) ∨ p2) ∧ (p1 ∧ (p5 ∨ p4))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219745910633423723472012025494 : ((p1 → (p5 → (p4 ∨ p1))) → (p3 → (False ∨ (((p5 ∧ (p5 → p1)) ∧ (p1 → ((((p5 ∧ p2) → p1) → (p5 ∨ p3)) ∧ False))) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205189985793989886712938800753 : (((p5 ∨ (p1 ∨ p1)) ∧ (p3 ∨ p2)) ∨ (((p5 → p3) → True) ∨ (False → ((((p2 ∨ p5) ∨ True) ∧ ((True ∨ p3) ∧ (p2 ∧ p2))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112566868936320425097380562375 : ((((True ∨ (p4 ∨ (((True ∨ (((p1 → p2) → p2) ∨ ((p3 → p3) ∧ p4))) ∨ ((p2 → p3) ∨ p5)) ∨ p2))) → p5) → p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638712915583885609323401743520 : ((((((p3 ∧ True) ∧ (p1 ∧ (True → p4))) → (((p2 → (True ∨ True)) ∧ p5) ∧ ((p2 ∨ ((p3 ∧ (p1 → True)) → True)) → False))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246499490276548831037669066707 : ((p5 ∧ p1) ∨ ((False ∨ ((((p5 ∧ p5) ∨ (True ∨ p4)) → (p4 → (((p2 → (p5 → p5)) ∧ ((p2 → p3) → p1)) ∨ p4))) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191191568196049267356086986837 : ((((False → p1) ∧ p1) → ((p3 ∨ (True ∨ p2)) → False)) ∨ (p4 ∨ (((p5 ∧ p5) → ((p4 ∨ (p4 → True)) ∨ p4)) ∨ ((p4 ∧ p5) ∧ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51725585465733299934546025762 : ((((False → (((False ∧ p3) ∧ p4) ∧ True)) → (p3 → (p3 ∨ ((p4 ∧ True) → True)))) ∧ ((((p2 ∧ False) ∨ (p1 ∨ p1)) → False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178497997904848532217820178654 : (((p4 ∧ ((p1 ∧ (p3 ∨ (p1 ∧ False))) ∧ False)) ∨ ((p5 ∧ False) ∧ p5)) ∨ (False → (((((p2 → p4) ∧ True) ∧ (p1 → p5)) → p3) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305707455813502429579008791756 : (p1 ∨ ((((p2 ∧ (p5 ∨ p2)) → False) ∧ (True ∨ (p4 → p3))) → ((((p3 → ((False ∨ (p1 → p2)) → p2)) ∨ p5) ∨ p3) ∨ (False → p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347425836043273897007868460976 : (p3 → ((True → ((p2 ∨ (p3 ∨ (p2 ∨ p3))) → p4)) → ((((True ∧ True) ∧ (p1 ∨ (p2 → (p2 ∧ p5)))) ∨ (p4 ∧ p1)) → (False ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ (p3 ∨ (p2 ∨ p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ (p3 ∨ (p2 ∨ p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57908310804666504655101035791 : (((p4 ∨ (p5 ∨ p5)) → ((p3 ∨ (p3 ∧ ((p1 → False) ∧ (p1 ∧ (p3 → True))))) ∨ ((((p2 → True) ∧ (p3 ∧ p2)) ∧ p1) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122900973268207414736649431091 : (((p4 ∧ (p3 ∧ (p3 ∨ ((p5 → ((((False ∧ p2) ∨ (True ∧ True)) → p3) → p3)) ∨ (p1 → p2))))) ∧ (p4 ∨ (True ∨ p4))) → (False ∨ True)) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259779875023607992044659609872 : ((p1 → p2) → (p1 ∨ (((True → p5) ∨ p3) → (((((p1 → True) ∧ (((p1 ∧ p3) ∧ True) → p1)) ∧ p2) ∨ (p1 ∧ False)) ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756411328772639454144893012259 : (((p1 ∧ ((p5 ∧ ((p4 → (((p2 ∧ p3) ∧ p2) ∧ ((False ∨ p2) ∨ (p1 ∨ (p5 ∧ (p2 → p3)))))) ∧ p3)) ∨ ((p4 ∧ False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768200075494674235665226688357 : (((p5 ∧ (((p2 ∨ (p4 → (p5 ∨ (p3 ∧ p4)))) ∧ (((p5 → (((True ∧ (True → p2)) ∨ True) ∨ p3)) ∧ p3) → True)) → (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138047299505763331325159648648 : ((True → ((p2 ∧ (p1 ∨ p1)) ∨ (((p4 → (((((p2 → p3) ∨ False) ∨ True) ∧ p2) ∨ p5)) ∨ (p3 → p2)) ∨ p3))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84633106254506689933597419675 : (((False → ((p4 ∧ (((p1 → p5) → True) → p5)) ∨ (((p1 ∧ p3) ∨ p4) ∨ p1))) → (((p1 ∨ (p2 → (p4 ∧ p1))) ∨ p2) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p4 ∧ (((p1 → p5) → True) → p5)) ∨ (((p1 ∧ p3) ∨ p4) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38684502384100970177136264020 : ((((p2 ∨ (p2 ∨ (p4 ∨ (p1 → p3)))) ∧ ((((True ∧ ((p5 → p2) → False)) ∧ p5) ∨ (p5 ∧ ((True ∨ p2) ∧ False))) ∧ False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179313789586253184389733086239 : ((False ∨ (p2 ∧ ((False → ((p1 → p2) ∧ p1)) ∨ (p1 → (p4 ∧ p4))))) ∨ (((((p1 ∨ p1) → p5) → (p5 ∨ p1)) ∨ p5) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185225947401119563892848825141 : ((False ∧ ((p1 ∨ ((p1 ∧ p4) ∨ (False ∨ p5))) ∧ (p1 ∧ p4))) ∨ (p4 ∨ (p4 ∨ ((p4 → (p3 ∨ True)) → (((p2 ∨ True) → False) → False))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600461369677534340463149321254 : ((((True ∧ (((((p4 → (p2 ∧ (p1 → p1))) ∨ (p5 ∨ p3)) ∨ p1) ∧ p4) → ((p2 → (p2 ∧ p5)) ∧ (p1 → (p5 ∨ p4))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56701291958804316360181835421 : ((((p2 ∧ p2) ∨ True) ∧ ((((p3 → True) ∧ (p2 ∨ False)) → (p3 ∨ p1)) → (((p1 ∨ p1) ∨ ((p3 → p3) → (p2 → p2))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60049560371332576919595477834 : (((p2 ∨ True) → ((p3 ∨ ((p5 ∧ ((p4 ∧ (p4 → (p4 ∧ True))) ∧ p3)) ∧ (p1 ∧ p5))) ∨ (((False ∧ (p5 → p5)) → True) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306645081387163542028602516838 : (p1 ∨ (True ∧ ((True → (((((p1 ∧ (((p2 ∨ p2) ∨ p4) ∧ p3)) ∧ (p5 → False)) ∨ p5) ∧ p4) ∨ (p1 → (True → True)))) ∧ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39116042012804389989901521613 : ((((p5 → p2) ∨ (((p1 ∨ p3) → ((False ∨ ((p3 ∨ ((p4 ∧ p1) → p3)) ∧ (False ∧ p1))) → False)) → ((True ∧ False) ∧ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591994188926447751145980241488 : ((((((True → p3) → ((((p1 ∨ p4) ∧ ((p5 → p4) ∨ p1)) → p4) ∧ (p5 → ((p1 ∨ False) → (p5 → p3))))) ∨ (p5 ∧ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172351646719967284736841649397 : ((((False ∨ (p3 ∧ (False ∧ p5))) ∧ True) ∨ (((p3 ∨ p2) ∨ p5) ∧ (False ∧ False))) ∨ ((p3 ∧ ((p3 ∧ False) ∧ p1)) → ((p3 ∧ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594607485686743111242173893995 : (((((p3 → (((p2 ∧ p4) ∧ (True → (p1 → (p4 ∨ (p2 → (p3 ∨ p1)))))) ∨ False)) ∨ (p1 ∨ ((p4 → False) ∨ (p2 → True)))) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157666284817121233743287295929 : ((((p5 ∧ ((((p5 ∧ p5) → False) ∨ p4) ∨ p1)) ∧ (True ∧ (True → p1))) ∨ (p3 ∨ (p5 → p2))) ∨ (((p1 ∧ p1) ∧ (p4 ∧ p5)) → p1)) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214554710145864763258317707924 : (((False ∨ p5) ∧ (p2 ∨ False)) ∨ (p1 ∨ ((((p5 ∧ True) ∧ ((p2 ∧ True) ∧ True)) ∨ True) ∨ (p2 → ((p5 ∧ ((p1 ∨ p4) → p1)) → p5))))) := by
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
theorem thm_5_vars_152058070494303733812339289177 : (((((p4 ∧ (p1 ∧ p2)) ∧ (p3 ∨ p1)) ∨ (True ∨ p1)) ∨ (p5 ∧ ((p5 → True) ∧ ((p2 ∧ True) → p4)))) → ((p1 ∨ (False ∨ p3)) ∨ True)) := by
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
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41036676151255113029283488277 : (((((p5 ∧ ((((((p2 ∧ (p1 → p1)) ∨ p5) ∨ p2) ∧ p1) → p5) ∨ False)) → (((p5 ∧ False) ∧ p5) ∧ p5)) → (p2 ∨ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164999255753034809688501557193 : (((((p5 → (p2 ∨ p4)) → (p2 ∧ (False ∨ p2))) ∨ (p5 ∧ ((p3 ∨ p3) → True))) → p1) ∨ (p2 → ((((p1 ∧ p3) ∧ p3) ∧ p3) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66479498188047855890662009091 : ((True → ((((((p5 ∨ p5) → (p5 ∨ p5)) ∨ ((p1 ∧ p1) → (p4 → (((False ∧ p3) ∨ p3) ∨ p4)))) → (False ∨ p4)) → p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311758256304232580689018682945 : (p2 ∨ (False ∨ ((((p4 ∧ (p5 ∧ ((True ∧ (True ∨ False)) → ((p4 → False) ∧ (False ∧ False))))) ∧ (True ∧ True)) ∨ False) ∨ (True ∨ (p1 ∨ False))))) := by
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
theorem thm_5_vars_110761465144148335105756638995 : ((((p1 ∨ (p5 ∨ ((((False ∨ (((p1 ∨ p4) → ((p2 ∧ p5) ∧ p2)) → (False ∨ p5))) ∨ p5) ∨ p1) → False))) ∧ p3) ∧ p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151884877441111845154150696158 : ((((((p2 ∨ (p4 ∨ p4)) ∨ ((p3 → (p4 ∨ p2)) ∧ p5)) → p4) → False) → (((p4 → p1) ∧ p1) ∨ p4)) → (p5 → ((p5 ∧ p1) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592376769374564888479877132784 : (((((((True → p3) ∨ (((p1 → ((p4 ∧ p5) ∧ True)) ∨ (False → p2)) → p2)) ∧ ((p5 ∧ (p1 → False)) ∨ p1)) → (p5 → p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614290219026718429025401726533 : (((((((True ∧ ((p4 → p2) → True)) → p3) ∧ (p2 → ((p1 ∧ ((p4 ∨ p2) ∨ True)) ∨ (False ∧ True)))) → (p5 ∧ (p3 ∧ p3))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699482908442915376848639654062 : ((((((p2 → (p4 → (p3 ∧ True))) ∨ (p4 → (p2 → p5))) ∨ p3) → (((False → True) ∧ (p5 → ((p3 ∧ p4) → (p1 ∨ p3)))) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105754424641234253466699169713 : (((p1 ∨ (((p4 → p3) → ((((p5 ∧ p1) ∨ (p2 ∧ p1)) ∨ True) ∨ p1)) ∨ True)) ∨ ((p4 ∧ ((p4 ∨ p1) ∨ False)) → p1)) ∧ (p2 → p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



