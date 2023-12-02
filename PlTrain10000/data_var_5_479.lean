variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188266218464010524313510767418 : (((p5 ∧ (p2 ∧ (((p4 ∧ p4) ∨ p1) ∨ p2))) ∨ True) ∧ ((p3 ∨ ((p2 ∧ (((p3 ∧ (False ∨ p4)) ∨ p4) ∨ p1)) ∨ (p5 → True))) → True)) := by
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
theorem thm_5_vars_157920942265002294373884927150 : (((True → (((p4 → (False ∨ p3)) → p1) ∧ (p4 ∧ True))) → (((p5 ∧ p3) → (p1 ∨ p3)) ∧ p2)) ∨ ((True → p3) → ((p1 ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877251619773317265309836868879 : ((((((p5 → p3) → ((True ∨ ((p4 ∨ True) ∨ False)) ∧ True)) → (((False ∨ False) → ((p4 → p2) ∨ (p2 → True))) ∧ False)) ∧ (p2 ∧ True)) → p1) ∧ True) := by
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
  have h6 : ((p5 → p3) → ((True ∨ ((p4 ∨ True) ∨ False)) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44608942337258036647753451321 : ((((p2 ∧ (((p1 ∨ p4) ∨ p4) → (p5 ∧ False))) → (p4 ∨ (p3 → (p5 ∧ (p5 → (p1 ∧ (((p3 ∨ p5) ∧ False) → False))))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232202919354358706371784063167 : (((False → p4) → False) → ((True ∧ (((p2 ∧ (p2 → (True → ((p5 → p5) ∧ ((p3 → False) ∨ (p4 ∨ False)))))) ∨ p1) ∨ (p4 → False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233582859805241861162476767920 : ((p1 ∨ (p4 → p2)) → (p5 → ((p5 → (p2 ∨ (p4 ∧ p5))) ∨ ((p2 ∧ (True → ((((False → p5) → p1) → True) ∧ p3))) → (p4 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330815878285628645129354864199 : (True → (p2 → ((p1 ∨ p5) ∨ (p3 ∨ ((((p2 → p1) ∨ (p5 ∧ (p2 ∧ p5))) ∧ (p3 ∨ (((p4 → p1) → p4) ∨ p5))) ∨ (p2 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179904752413248878362523596221 : (((((p4 → (((p5 ∧ p1) → p2) ∨ (p5 ∨ p1))) → p1) ∨ p4) ∨ p4) → (((p1 ∧ (p2 ∧ (p4 ∧ (False → True)))) → p2) ∨ (True ∨ p3))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172986080240810284789133993039 : ((p5 ∧ (((p5 ∨ ((p4 ∧ p1) ∨ p1)) → ((p5 ∧ False) ∧ (p3 ∧ True))) ∧ p5)) ∨ (p5 ∨ (((p5 ∧ p3) → p2) ∨ ((p4 ∧ p4) → True)))) := by
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
theorem thm_5_vars_323284488137426480255251281280 : (p5 ∨ (((((p5 → p4) ∨ ((p2 ∧ p4) ∨ (p3 ∨ ((p5 → True) → (p3 ∨ ((p5 ∨ p4) → (p1 → p1))))))) ∨ p2) ∧ p1) → (p5 ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715739975409743933345194042727 : ((((((p2 ∧ False) ∨ p2) ∨ False) ∧ (p5 → (p1 ∨ (((p5 → p5) ∨ (p1 → ((p2 ∨ (p4 ∨ p4)) ∧ p5))) → ((p1 → p1) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184752863508558030029475404314 : ((((p2 → p3) ∨ (p3 ∧ p3)) ∧ ((p4 ∧ p4) ∨ (p4 → p3))) ∨ ((p1 ∨ ((True ∨ (False → p1)) → p3)) ∨ ((p5 ∧ p4) → (p1 ∨ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198334267914683388571061037081 : ((p2 ∧ ((p2 ∧ ((p5 ∨ p2) ∨ True)) ∨ p5)) ∨ ((p5 → True) ∨ ((((True ∧ (((False ∧ (p1 ∧ p2)) ∧ p4) ∨ True)) → p3) ∧ p4) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249058310793131884646257137927 : ((p4 ∨ p1) ∨ ((((p5 ∨ (((p3 ∨ p5) ∧ ((((p5 ∨ p4) ∧ (False ∨ p4)) ∧ p3) ∨ False)) ∨ (False → p2))) ∧ p3) ∧ p1) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152972366550992722767383857695 : ((p1 ∧ ((p4 ∨ ((p5 ∨ p4) ∧ ((True ∨ (p1 ∧ False)) → (True ∧ ((p1 ∨ True) → p3))))) ∨ (p4 ∧ False))) → ((p1 → (False ∧ False)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159195090711334286218014294358 : ((p2 → (((False ∧ True) ∨ ((p3 ∧ ((p2 ∧ (p3 ∨ (p2 ∧ p4))) → True)) ∧ (False ∨ True))) ∨ p5)) ∨ ((True → (p1 ∨ (True → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63269567886360259454376009216 : ((p5 ∧ ((((p4 ∨ True) ∧ (p4 → p3)) ∨ p1) → ((p3 ∨ p1) ∨ ((p2 ∧ (p4 → (False ∨ ((False ∧ p4) ∨ False)))) ∧ (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791675807263739376855563286152 : (((True → (((True → ((((p5 → p3) ∧ (p5 ∧ True)) ∨ p1) ∨ p1)) → (((p5 → ((p5 ∨ p4) ∨ True)) ∧ (p1 ∨ False)) ∨ False)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47533310200698836238331588473 : (((p4 ∨ ((p4 → ((p1 ∨ (p5 ∨ p3)) → p3)) → (p2 ∧ ((p3 ∨ (((p1 ∨ (True → False)) ∨ p2) ∧ p5)) ∨ p4)))) ∨ (p1 → p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307447820287760970749963844726 : (p1 ∨ (p5 ∨ ((p5 ∧ (((True ∨ True) ∧ False) → (p2 → (False ∨ p2)))) → (p1 → (p2 ∨ ((p3 → (((False ∧ p4) ∧ p5) ∨ p3)) ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112724825144490238403354520939 : ((((p2 → ((p4 → p3) → (p5 → (False ∧ (p1 ∧ ((p4 ∨ p4) → p2)))))) ∨ ((((p5 ∧ p2) → p3) → p3) ∧ p4)) → p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748649882772071483488418424277 : ((((p3 → p2) → (p4 ∨ ((p5 ∧ p3) ∨ ((p3 ∨ p5) ∨ ((True ∨ (False → (False → p3))) ∨ (p3 ∧ (p2 ∨ ((p4 ∨ p5) ∧ p5)))))))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127555163845684477592829721202 : ((p4 ∨ ((p4 ∨ (p2 ∨ (p1 ∨ True))) ∧ (((((p1 ∧ p1) ∧ (p1 ∨ p1)) ∨ (p1 → (p3 ∧ (p3 ∨ True)))) ∧ p2) ∧ p4))) → (False ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h5.left
        let h22 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h5.left
          let h36 := h5.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- Conjunctions on the left can always be decomposed.
            let h42 := h40.left
            let h43 := h40.right
            -- Disjunctions on the left can always be decomposed.
            cases h41
            case inl h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h36
            case inr h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h36
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h5.left
          let h49 := h5.right
          -- Conjunctions on the left can always be decomposed.
          let h50 := h48.left
          let h51 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h50
          case inl h52 =>
            -- Conjunctions on the left can always be decomposed.
            let h53 := h52.left
            let h54 := h52.right
            -- Conjunctions on the left can always be decomposed.
            let h55 := h53.left
            let h56 := h53.right
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h57 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h49
            case inr h58 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h49
          case inr h59 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355880322323163173183353737885 : (p5 → ((p4 ∧ ((p4 ∧ (p2 → (p1 → ((p1 ∨ ((p5 ∧ False) ∧ (p5 ∨ p5))) ∧ ((p4 ∧ p4) ∧ p3))))) ∨ False)) ∨ ((p2 ∨ False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105507760282918457080256001250 : (((p1 ∨ (p5 ∨ (p4 ∧ ((p5 ∧ p4) ∨ ((((p5 → p2) ∨ p2) ∨ p1) ∧ (True ∧ True)))))) ∨ (False → ((False ∨ True) ∧ p4))) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58287697096818208234350190459 : (((True ∨ p1) ∧ (((((((True ∧ (p4 ∨ p1)) → p5) → (False → ((True ∧ p1) ∨ p2))) → p1) ∨ p2) ∨ ((p5 ∨ p2) ∧ p2)) ∨ True)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683882825289927647603715790091 : (((((p2 ∨ (p1 ∨ ((((((p5 ∨ (True ∨ p2)) ∨ p1) → p1) ∨ p4) → False) ∨ False))) ∨ True) ∨ ((True ∨ False) ∧ ((p1 ∨ p2) ∨ False))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226278792494878462166216101426 : (((p4 ∨ False) ∨ p3) ∨ (((p5 ∨ (((True ∨ p2) ∨ (p1 ∧ (p4 ∧ p3))) → (p2 ∧ True))) ∨ p3) ∨ ((False → ((p1 → p5) → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788139772462839539366388447893 : (((p5 ∨ ((((p1 ∧ p3) → ((p4 ∧ p1) ∨ (p1 → ((p5 ∨ p4) ∨ p3)))) ∨ (p2 ∧ ((True ∧ True) ∨ ((p4 ∨ p1) → p4)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134194212323674101126390280421 : (((((p4 ∨ (p1 ∧ p2)) ∨ ((p5 → (False ∧ p4)) → p2)) ∧ (p5 → ((p5 → ((p1 ∨ p4) ∧ p4)) ∨ p3))) ∨ True) ∨ ((p2 ∨ p5) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172440336782868905505589776858 : ((((False ∨ (p2 ∨ p5)) ∧ p4) ∨ (p1 ∨ (((p3 ∧ p5) → True) ∧ (True ∨ p1)))) ∨ (p2 → (((True ∨ p3) → (p3 → p5)) ∨ (False ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112895715047091044701599994561 : ((((p1 → p1) ∧ ((((True ∧ ((p1 ∨ p4) ∨ True)) ∧ (False ∨ False)) → (((p4 ∧ p1) ∨ p3) ∨ (p3 ∨ p5))) ∨ p4)) → p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57966086487495126689252269339 : (((p2 → (p4 → True)) → ((p2 → (True ∧ (p2 → ((((((True ∧ p2) ∨ p4) ∧ False) → (p4 ∨ p5)) ∨ p5) → (False ∨ False))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111876354258175607467534328612 : (((((p3 ∨ (((False → (p4 ∧ (p5 ∧ (p1 ∧ (p1 → True))))) ∨ p1) ∨ p4)) ∨ p1) → ((p2 ∨ True) ∧ (p2 ∨ True))) ∨ p1) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
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
theorem thm_5_vars_49242704983553806481832598590 : ((((p4 ∨ False) → ((p1 ∨ ((((False → (p5 ∨ (p4 ∨ p1))) ∨ (p3 ∨ p1)) ∧ (p3 → True)) ∧ p3)) ∧ p3)) ∨ (True ∨ (p3 ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64926352111959042187930579083 : ((p2 ∨ (((((p4 ∧ True) → p4) ∨ (p5 → (p5 ∧ True))) ∧ (p2 ∨ (p1 → False))) ∧ ((p3 ∨ (((False → True) ∨ False) ∧ False)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41807961060275898402676137563 : ((((p4 → (p5 → (p1 ∧ p4))) → ((p2 ∨ (p3 ∧ p2)) → (((((False → p3) ∨ True) ∨ p5) ∨ (False ∨ (p1 ∨ p3))) → p3))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38827149128028142294747658807 : ((((p3 ∨ ((False → p1) → False)) → ((p3 ∨ (p5 ∧ p4)) → (p4 ∨ ((((p2 ∨ False) ∨ (False ∧ p1)) ∧ (p2 → p5)) ∧ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37722411933220754987309056981 : (((((((p3 ∨ ((((p3 ∧ p4) ∧ (True → p1)) ∨ p1) → True)) ∨ True) ∧ p5) → ((p3 ∨ (p3 ∨ (p3 → p4))) ∧ p4)) → p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320524410518759527548515065635 : (p4 ∨ (True ∧ ((True ∧ (((p1 ∧ (p1 → p4)) → p1) ∧ ((p3 ∧ p5) ∨ (p3 ∨ p2)))) ∨ ((p3 → p3) ∨ (((p4 ∧ p3) ∨ False) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302030778223636789599543604961 : (False ∨ (True ∧ (((p5 → True) → (((p1 → p3) ∨ p2) ∧ ((False ∧ (p4 → p1)) → (p1 → True)))) ∨ ((True ∧ p2) → ((True ∨ p3) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313061258548096509032472256093 : (p3 ∨ (((True ∨ (((p3 ∧ (p2 ∨ (p3 ∧ p3))) → (p5 → p1)) ∧ (p5 ∧ (((p4 ∨ True) ∨ (False → p3)) → (p5 ∧ p4))))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229037925007242563361013229078 : ((p5 ∨ (p1 ∨ p1)) ∨ ((p3 → ((((False → False) → p3) ∧ (((p2 → p1) ∧ p4) ∨ p3)) ∨ (p5 → (((p4 ∧ True) → False) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686618068980250033651880329782 : (((((True → True) ∨ ((p3 ∧ (((True ∨ True) → (True ∧ (p4 → (True ∧ p4)))) → p3)) ∨ False)) → ((((p4 ∨ False) ∧ p5) ∨ True) ∨ p5)) ∨ p3) ∧ True) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776779719036490130130149622236 : (((p1 ∨ ((((((p4 ∧ (p1 → ((False ∨ p5) ∧ False))) ∨ (p4 → p5)) → p2) → True) ∨ (p3 ∧ ((p3 → (p1 ∧ p1)) → p4))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47196349779401134452617937133 : ((((p2 → ((p4 → ((p3 ∨ False) ∨ (p4 ∧ p3))) ∧ (p1 ∧ False))) ∨ ((((p4 ∨ (p1 → p1)) ∧ True) → False) → p4)) ∨ (p4 ∧ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (p1 → p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589401877951220960240148368345 : (((((((p1 ∧ ((p3 ∨ (p5 ∧ True)) ∧ ((True ∨ p1) → (p2 ∧ (p1 → False))))) → ((p3 ∧ p3) ∧ (False ∨ p3))) ∨ True) → False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233520883098057933272460176317 : ((p1 ∨ (False ∨ p2)) → (p1 ∨ ((((p1 ∧ p1) ∧ p5) ∨ (((p4 → (p3 ∨ p4)) ∨ ((True → p4) → p3)) ∨ (p4 → (False ∧ p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62690403526491200419795006703 : ((p4 ∧ ((((False ∨ p3) ∨ (((((False → p5) → p5) ∧ (p2 ∧ (p5 ∨ (p4 ∨ (p2 ∧ True))))) → p1) ∨ (p1 ∧ p2))) ∨ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209101854100145828701395337204 : ((p2 ∨ ((True ∨ p5) ∧ (p3 ∧ p4))) → ((p5 ∧ (p2 ∧ (False ∧ p4))) ∨ (p1 → (p3 ∨ (False → (True ∨ (((p5 ∨ p3) ∧ p1) ∧ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h7.left
      let h14 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2930130916626205353742419102 : (((True → True) ∧ p1) ∨ (((p1 ∨ p3) ∧ p3) ∨ ((p1 → (((True ∨ p4) → (p2 ∨ (True → p3))) ∨ p1)) ∨ ((True → p5) → True)))) := by
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
theorem thm_5_vars_144558498509176187138793920868 : ((((False ∨ (p5 ∧ p1)) ∧ ((((p4 ∨ p4) ∨ (p2 ∧ True)) ∨ (True ∧ (p3 ∧ False))) ∧ True)) ∨ (False → False)) ∧ (((p4 ∧ True) ∨ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713233596271977948152285739320 : ((((p3 ∨ (((p5 ∨ p1) ∧ p1) ∧ p5)) ∨ ((False ∨ ((p5 ∨ p5) ∨ (p3 → p3))) ∨ (True → (True ∧ ((p4 ∧ p3) ∧ (True → True)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731333303261114001295876548842 : ((((p4 ∨ (p2 → True)) → ((p2 ∨ p3) ∨ (p1 ∨ ((False ∧ p2) ∨ ((((p4 ∨ (p2 ∨ (p2 → False))) ∨ p1) ∧ p4) ∨ (p1 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215315088006279408184151901267 : ((p1 ∧ ((p4 → p1) → True)) ∨ ((p4 → ((p3 ∨ ((p3 ∨ (p3 ∨ (p2 → p4))) → (((p3 ∧ p3) ∧ (True → p2)) ∧ p4))) ∨ p4)) ∨ p4)) := by
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
theorem thm_5_vars_172554859314872996615000521062 : ((((p5 ∨ True) → p3) ∨ ((p4 ∨ (p3 → (p1 → (p2 ∧ True)))) → (p5 → p1))) ∨ ((False ∨ (p1 ∨ (False ∨ ((p1 → False) → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51572904413674602765164274957 : (((p3 ∨ ((p3 ∨ ((False → (False ∨ (((p3 ∨ p4) ∧ p5) ∨ True))) ∨ p4)) ∨ (p1 ∨ p3))) → (p3 ∨ (p5 → (True → (p4 ∨ p5))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- Implications on the right can always be decomposed.
          intro h9
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654732724264533397960081278282 : ((((((p3 ∧ (p5 → (((((p3 ∨ p2) ∧ ((p3 → p2) ∨ p2)) ∧ (p5 ∨ (p5 ∧ p3))) ∨ p3) → p5))) ∨ True) → p5) ∨ (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_298901226830471147561706543432 : (False ∨ (((True ∨ ((p3 ∨ p1) → p4)) ∧ (p2 ∨ (p1 → (((p3 ∧ p5) ∧ False) ∨ ((p1 ∨ (True → (True ∨ (p5 ∧ p2)))) ∨ p4))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118762124189801069454033153884 : ((p5 ∨ ((p4 ∨ True) → (((p1 ∧ ((p1 ∨ p4) ∨ p2)) ∧ p5) ∨ (((((p4 ∧ False) ∧ True) ∧ False) → p4) ∧ (p3 ∧ False))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147370561795397019340191640815 : (((((p5 → (False ∨ p3)) ∨ (((p1 ∧ p3) → p3) → (p4 ∧ p5))) ∨ ((True → p3) ∧ (p5 ∧ p5))) ∨ p4) ∨ ((p3 ∨ False) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184010503561636050337329733947 : ((((((p3 ∧ False) → p4) ∧ ((True ∨ False) → p5)) ∨ p5) ∨ p4) ∨ ((p3 → True) → ((p2 ∧ (p5 ∧ (True → ((p1 → p1) ∧ False)))) → False))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46022527896762141570880910512 : (((((p1 ∧ False) ∧ (p4 → (p5 ∨ (((p3 ∨ (p1 → (False ∨ (p1 ∨ p2)))) ∧ p1) ∨ ((p5 ∨ p1) → True))))) ∧ False) ∧ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179146984328500557275436053336 : ((p2 ∧ ((((p2 → (p2 → (p4 ∧ False))) → p2) → (p5 ∨ False)) ∧ p4)) ∨ (((p1 → (True ∨ (p2 → (p2 ∧ (p1 → False))))) ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136492723728565105546840025981 : ((((p5 ∧ False) → True) ∧ (((p4 → (p1 ∧ p4)) ∨ ((p5 → (p5 ∧ p4)) ∨ p4)) → ((p1 ∨ False) ∨ (p5 ∧ p1)))) ∨ (False → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191015550787642548145529740725 : (((True → ((False ∨ p5) ∧ True)) ∨ ((p3 → p2) → False)) ∨ ((((p1 ∧ (p3 ∧ (p1 → (p1 → True)))) → ((p5 → p4) ∧ p4)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694394967348201308287924260897 : (((((p4 → p4) ∧ ((((p4 → False) ∨ (p1 ∨ (p5 ∧ p5))) ∨ p2) ∧ p2)) ∨ ((p1 → (p2 → p1)) ∨ ((p4 ∧ p1) ∨ (p5 ∨ p5)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305010329759974840076069548678 : (p1 ∨ (((((p2 → (p2 → True)) → p2) ∨ p1) ∨ (p3 → (((False ∨ True) → p5) → ((p3 → (p5 → p2)) → p2)))) ∨ ((False ∨ p1) ∧ p4))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595342374421665423881961497494 : ((((((p2 ∨ (True ∧ p1)) ∨ (True → ((p4 → (p5 → p2)) → True))) ∧ (((((False → (p4 ∧ p1)) ∧ p2) ∧ False) → p4) → p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783109870227192714025203356889 : (((p3 ∨ ((p1 → ((((((p3 ∧ False) → p4) → p3) ∧ p5) ∨ (p1 → ((False → True) ∨ (p1 ∨ p1)))) ∧ (p5 ∧ p4))) → (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53094901513580137559106333141 : (((p3 ∨ (((p4 → ((False ∨ (p5 ∨ p4)) → p4)) ∨ False) → p3)) ∧ (((p3 → p3) ∧ (False → (p4 ∨ p3))) ∧ ((p1 ∧ p4) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310207527468207248934988711721 : (p2 ∨ (((p2 ∨ ((True ∧ False) → (p4 ∨ (p5 → (p4 ∨ p4))))) → p4) ∨ (p5 → ((False ∨ True) ∧ ((((p3 ∨ p2) → p2) → p1) → p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253030674062155335812639700090 : ((True ∧ p3) → ((True → p4) → (((p3 ∧ (False ∨ (p4 → (p1 → (((((p5 → p3) → p4) ∨ p5) ∧ (False → p4)) ∧ False))))) ∨ False) ∨ p3))) := by
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
theorem thm_5_vars_40708175444275257700536394761 : ((((((False ∨ (p3 → ((p4 → False) ∨ False))) → (False ∨ p3)) ∧ ((p2 ∨ (((True ∧ (p4 ∧ p4)) ∧ p4) ∧ p5)) → False)) → p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56883914101903271178641315036 : (((p2 ∧ (False → True)) ∧ (((p4 → ((False ∧ p1) ∧ p4)) → ((p3 → ((p3 → p3) → True)) ∧ ((p2 ∨ p2) → p4))) ∧ (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219345035291933360740960964678 : ((p2 ∨ (p2 → (p5 → p3))) → (((((((p3 ∨ ((p5 → p3) ∨ p1)) → p1) ∧ p4) ∨ p5) ∧ p5) ∨ p4) ∨ (p3 ∨ ((p1 ∧ True) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811977502845000823589995371782 : ((((((True → ((p2 ∨ (((p3 ∧ p4) → ((p4 → (((p4 → p2) ∨ p1) → False)) → (p5 ∨ False))) ∧ p1)) ∧ False)) ∧ p2) ∧ p3) ∧ p3) → p5) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265559897260946170265414517458 : (True ∧ (False ∨ (p5 ∨ ((p4 ∨ (((True ∧ p5) ∧ (p2 → (False → False))) ∧ p3)) ∨ (((p5 ∨ p4) ∨ (p3 → (True ∧ p3))) ∧ (True ∨ True)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349468481261470861013382681705 : (p3 → (p5 → ((p4 ∧ (((p1 ∧ p4) → (((False ∧ False) ∨ p2) ∨ ((p2 ∨ p5) → (p4 → ((p3 → p3) → p5))))) → False)) ∨ (p2 ∨ p3)))) := by
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
theorem thm_5_vars_590175912266687474335405386505 : ((((((p5 → (((p3 ∨ (p4 ∧ p5)) ∧ p3) ∧ p3)) → (((((p3 → p2) → p2) ∨ (p1 → p5)) → p3) ∨ (p1 ∨ False))) → p4) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40768674831328192052510411310 : (((((p5 ∨ p5) → (((((True ∧ True) ∨ ((False → False) → p1)) → (p2 → p3)) ∧ p1) ∨ (p4 ∧ ((False → p3) → True)))) → p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299447511260475513091090044867 : (False ∨ ((p2 ∨ (((p5 ∧ p5) ∨ (p4 ∧ (p2 ∨ True))) → (((p3 → (p1 ∧ p1)) ∨ ((p2 ∨ True) ∨ p5)) → (p2 ∨ (p3 → p3))))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h35
            -- One of the premise coincides with the conclusion.
            exact h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h46
          -- One of the premise coincides with the conclusion.
          exact h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93230121002856155892956565370 : ((True ∧ (True → ((p2 ∨ (False ∨ ((p2 ∧ p3) → p2))) ∧ ((((p5 ∧ p1) ∨ (p3 → (True ∧ True))) ∨ p2) ∧ (False ∧ (False ∨ p1)))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149261476905719945564389385836 : (((p4 ∨ p4) ∨ (((p3 ∧ (p3 ∧ p2)) ∧ p4) ∨ (p4 → (False → (p4 → ((p5 ∨ False) ∨ (p3 → False))))))) ∨ ((False ∨ p4) → (p1 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180728966624168542206005986641 : (((p4 → (p3 → (p4 ∨ False))) ∧ ((p1 ∨ ((False ∧ p4) ∨ p2)) ∨ p5)) → (p2 → ((False ∨ (p1 ∨ p3)) ∨ (True ∨ ((p3 ∧ False) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778620348331145980347134803699 : (((p1 ∨ (p1 ∨ (((p3 ∧ p1) → (p1 ∧ (((((p2 ∧ p5) ∧ (p3 → p3)) ∨ p1) ∨ ((True ∧ p5) → p3)) ∨ p5))) ∧ (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761510308383675440840070479379 : (((p3 ∧ ((((((p1 ∨ True) ∨ (p2 ∧ p3)) → ((True ∧ p5) ∨ (p1 ∨ (p1 → (True ∨ (p4 ∧ p5)))))) ∨ (False ∨ False)) ∧ p4) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315575339639209986835842552782 : (p3 ∨ ((p2 ∨ True) ∧ (((False ∧ p1) ∨ p2) ∨ (((p5 ∧ (p2 ∧ (True → True))) ∧ ((p4 ∧ p3) ∨ (p5 ∨ False))) → (p2 → (p1 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354914020827561054955221665196 : (p5 → ((False ∨ (p2 ∧ (p3 ∧ (True → (((p3 ∧ False) ∨ ((p5 ∧ p4) ∨ (p3 ∨ p4))) → (False ∧ (p5 ∨ ((p4 ∧ True) ∧ True)))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114384920097812450789468788701 : ((((p2 ∧ (((True ∨ p4) ∨ p2) ∧ (p4 ∧ (p2 → ((True ∨ p3) ∧ p3))))) ∧ (p5 ∧ p3)) ∨ (p2 → (p3 → (p4 ∨ p3)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114501847772912261430328431790 : (((((True ∧ (p4 → p5)) ∧ p2) → (((p2 → (p1 ∧ p2)) ∨ p5) → ((p1 ∧ p1) ∧ p1))) → ((p1 → (p3 ∨ p4)) ∧ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301523220495037685280489370524 : (False ∨ (((p3 ∨ p2) ∧ True) ∨ (((((False ∧ p1) ∧ p3) → ((p1 → (p5 → (p4 ∨ (p3 ∨ False)))) → True)) → False) → (p4 ∧ (True → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p1) ∧ p3) → ((p1 → (p5 → (p4 ∨ (p3 ∨ False)))) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((False ∧ p1) ∧ p3) → ((p1 → (p5 → (p4 ∨ (p3 ∨ False)))) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625986249586474645003156339710 : ((((p2 → ((p3 ∨ (((p3 → True) ∧ (p1 → False)) → p2)) ∧ (((p5 ∨ (True ∧ p4)) ∨ p4) → ((True ∨ (p3 ∨ False)) ∧ p3)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1977949959239433276121728587 : ((p5 ∨ (((((True ∧ ((p3 ∧ p2) ∧ p1)) ∨ False) ∨ (True ∨ p3)) ∨ ((p1 → p4) ∧ p3)) ∨ True)) ∨ ((False ∧ (p3 ∨ True)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180567383483753189473729579480 : (((((True → False) ∨ ((p1 → p1) ∧ p2)) → False) → (p3 → (p3 → p3))) → (p2 ∨ ((True ∧ (False ∨ ((p5 → p1) ∨ (p4 → p4)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156929138166374269956130591497 : ((((((p4 ∧ ((p5 → p5) ∨ ((True ∨ p4) ∧ p4))) → (p3 ∧ False)) ∧ p5) ∧ (p5 → p4)) ∨ True) ∨ (True → ((p5 → p5) ∧ (p1 ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328200445189389766394568598305 : (True → (((p4 ∧ False) ∨ ((True ∧ ((((p3 ∨ False) → p4) ∨ (p5 → (p1 → p5))) ∨ (p1 ∧ True))) ∧ (True → p4))) → (p2 ∨ (False ∨ True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780752450176517450765390278147 : (((p2 ∨ ((((p1 ∨ (p3 ∨ p4)) ∧ p3) ∨ p1) → ((((((p5 ∧ p5) ∧ p5) ∧ (p5 ∨ p1)) → False) ∧ ((p5 ∧ p5) → p4)) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178470573678328002187090104289 : (((((p1 ∨ p4) ∨ ((False ∧ p2) ∨ p2)) ∧ p2) ∨ (True ∧ (True ∧ p3))) ∨ (p5 ∨ (((False ∨ p3) → False) ∨ (p4 ∨ (False → (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178920801483528838880483816542 : (((p2 → False) ∧ (p4 ∨ ((((True → p2) → (p5 ∧ p2)) ∨ True) ∨ True))) ∨ (p2 ∨ (False ∨ ((p1 ∧ p1) ∨ (True ∨ (p2 ∨ (p2 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



