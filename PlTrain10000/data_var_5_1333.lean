variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67582702617242357903563427838 : ((p1 → ((p1 ∨ p2) → (((p3 ∨ (p5 ∧ p4)) → (p2 ∧ p4)) ∧ (((p2 → False) → (p4 ∨ (p3 ∧ (True ∧ False)))) ∨ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651923435870419240518900872459 : (((((p3 → p2) → ((p5 ∨ (p2 → ((p5 → (p2 ∨ ((p5 → (p2 ∨ ((False ∨ False) ∨ p3))) ∧ False))) ∨ p1))) → p2)) ∧ (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54005630876911783585238849077 : (((((p2 → ((False → p4) ∧ (p4 ∧ p1))) → True) → p3) → (((p4 ∨ ((p1 → p3) → p3)) → (False ∨ (p4 → (p2 ∧ True)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338050284021627801032225439441 : (p1 → ((False ∨ (p5 ∨ ((p3 ∨ ((True → p4) → p2)) ∧ False))) ∨ (((p3 ∨ False) ∧ ((p5 → (p3 ∧ True)) → (p5 ∨ True))) ∨ (p1 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219069010874198172318696981439 : ((p5 ∧ (p2 ∨ (True → True))) → ((True → (((p3 → p2) ∨ (p5 ∧ p4)) ∧ p2)) → (((p5 → (p4 ∨ False)) ∨ ((p2 ∧ False) → p1)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711720884025357515597259678616 : (((((((p4 ∨ p1) ∨ p5) ∧ p2) ∧ p4) ∨ ((((p4 ∧ ((p5 → (p3 → (True → True))) ∧ p5)) → p5) ∧ (False ∨ True)) ∨ (p2 → p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113413971593175650536069147238 : ((((((p3 ∨ (p4 → (((p1 ∧ (p3 ∧ (p5 ∧ (True ∨ p4)))) ∨ p1) ∨ p1))) ∧ False) ∨ (p4 ∨ p4)) ∧ p2) ∨ (p5 ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337061784293001889204223678090 : (p1 → (((((p5 → (p4 ∧ (p3 ∧ p2))) → p3) ∨ ((((False ∧ ((p4 → p1) ∧ p3)) → p4) ∧ (p3 ∨ p1)) ∧ p3)) → p4) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148193380421300302166307592215 : ((((p3 ∧ (True ∧ False)) ∧ ((((True ∧ p1) ∧ (p4 ∨ True)) → False) → (p1 ∨ True))) ∧ ((p1 → p1) → False)) ∨ (((p5 ∧ p4) ∧ p2) → p5)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200733038406343154710842772838 : ((p3 ∧ (((False ∨ p2) → p5) ∧ (p5 → p3))) → ((((p3 → p2) ∧ (p5 ∧ p3)) → (p2 ∨ False)) ∧ ((p5 ∧ False) ∨ ((p4 ∧ p4) ∨ True)))) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
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
theorem thm_5_vars_148045104378154596563145756030 : (((p1 ∧ (((False ∧ True) ∨ (p1 ∨ False)) ∨ (False ∧ ((False ∧ (p2 ∧ True)) → (p1 → p4))))) ∨ (p1 ∨ p2)) ∨ ((False ∧ (p2 ∨ p2)) → False)) := by
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
theorem thm_5_vars_205481055189607876267167010843 : (((True ∧ p5) ∧ (p4 ∧ (p5 ∨ p3))) ∨ ((((((False → p1) ∨ (p3 ∨ ((p5 ∧ p1) → p3))) → p1) → ((p1 → p5) ∨ p1)) ∨ p3) ∨ p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p1) ∨ (p3 ∨ ((p5 ∧ p1) → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702008839030578023528561643477 : ((((p5 ∨ (p5 ∧ (((True ∧ p5) ∨ p1) ∨ (p3 → p5)))) ∧ ((False ∧ (p4 ∨ ((p4 ∨ (p3 → p3)) ∨ ((True ∧ p2) → p4)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387163784204384925174223461703 : ((((((((False → p1) ∧ True) → False) ∨ (p2 ∧ ((p3 → ((True → p2) ∨ (p2 ∨ (True → p3)))) → p4))) ∧ (p4 ∨ (True ∨ p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_181603522921374102043453395248 : ((p2 → (((((p4 → p3) → (p5 ∨ p3)) ∧ (p3 → p1)) ∨ True) ∧ False)) → (((((p5 → False) ∧ p1) ∧ p2) ∧ (True ∧ (p3 ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313934631713916213591340465920 : (p3 ∨ ((((((p5 ∨ (p3 → (p1 ∧ p2))) → p5) → (p2 ∧ (p1 ∧ p2))) ∨ (p3 ∧ (((p1 ∨ p5) ∨ False) ∧ p4))) ∨ True) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161768892821260522403584549785 : ((p4 ∨ ((p4 ∧ (False → ((p2 ∨ p4) → p5))) ∨ (True ∨ ((((p3 → p4) ∧ p2) ∨ p5) ∨ p4)))) → ((False ∨ (p5 → (p5 ∨ p2))) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184429941479593126392858797555 : ((((p5 ∨ (p5 → False)) ∧ ((p3 ∨ p5) ∧ p3)) ∧ (p4 ∨ p4)) ∨ ((True ∨ (True ∧ p4)) → ((True ∨ True) → (p1 ∨ (True ∨ (p2 → p1)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227094184721355615069428620943 : (((p3 ∨ p5) → p3) ∨ (((p2 ∧ ((p5 ∧ p2) ∨ ((False ∨ p3) ∧ p2))) ∨ False) ∨ ((p1 ∧ ((p3 → (False → p1)) ∧ (p3 ∧ p3))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149414897909114851525697209617 : ((True ∧ ((p1 ∧ (p5 → (((p5 → p2) ∧ p3) ∧ p3))) ∨ (p3 ∧ ((p3 ∨ (False ∨ (p5 ∨ p5))) ∨ p4)))) ∨ ((p4 ∧ False) → (p4 ∨ p4))) := by
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
theorem thm_5_vars_192055821126030396926043492182 : ((p3 → ((((p3 ∧ p1) ∨ p1) → (p4 ∨ p5)) ∨ False)) ∨ ((((p2 ∧ p3) ∧ (p2 → (p1 ∨ (p2 ∨ ((p3 ∧ p1) → False))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186803042838817100608622168035 : ((((False → p4) → (False ∨ False)) ∧ ((p4 → (True ∨ p3)) → p1)) → (p4 ∧ ((False → (((p3 ∨ (False ∨ p4)) ∨ p5) ∧ False)) ∧ (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h9
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h14 := h10 h12
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h21 := h17 h19
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780975567585331386362541512261 : (((p2 ∨ (((p2 → False) → p5) → ((p5 ∨ p4) ∧ ((p3 ∧ (p2 ∧ (p3 → (p5 ∨ True)))) ∨ ((((p4 ∧ True) ∧ p5) → p2) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183974619602291790805181069120 : (((p4 → (p4 → ((False → (p4 → (p2 ∧ True))) ∨ p4))) ∧ False) ∨ ((p5 → (((p5 ∧ p1) ∨ False) ∧ ((False → p3) → (p3 ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246252541547807788245451423672 : ((p4 ∧ p4) ∨ (((((((p2 ∧ (False ∨ p1)) ∨ (((p5 ∨ False) ∧ (p3 → False)) → ((p4 ∧ True) ∨ p2))) → False) ∨ p2) → p2) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37711917587473503699805951590 : ((((((p2 ∧ ((((p4 → p4) ∨ ((p2 ∨ p2) ∧ (p2 → p5))) → True) ∧ p1)) ∨ p5) ∨ (True → (p2 ∧ (p3 → False)))) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317814168009777182328081555709 : (p4 ∨ (((p2 ∧ (p1 ∨ ((p4 ∨ p3) ∧ p4))) → (False ∨ (((p2 ∨ False) ∧ ((False → (p5 ∨ p5)) ∧ (True ∨ (False ∨ p2)))) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62885015161857095369560342616 : ((p4 ∧ ((p2 ∨ p2) ∧ (p1 ∧ ((p3 → ((p4 → ((False → (p2 ∨ (False → (p2 ∨ (False ∧ True))))) → True)) → (p2 ∨ p5))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172311214788515386220678801310 : (((p1 ∧ ((p4 ∧ p2) ∨ (True ∧ (p5 → True)))) → ((p5 ∨ (p4 ∨ False)) ∨ p2)) ∨ (p5 → (p4 → ((p5 ∨ True) ∧ (True ∨ (p4 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177834932464712358172823126501 : (((((((p5 → p1) → p4) ∨ (p1 → (p2 ∧ p2))) → p5) ∧ p2) ∨ True) ∨ (False → ((p4 ∧ ((p5 → p1) → ((p3 → p4) → p1))) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153674039375931148190334804699 : ((p2 → (((((p3 ∧ True) ∨ False) ∨ False) → ((p1 → p1) ∧ (p1 ∧ ((p3 → p4) ∨ p3)))) → (p2 ∨ p4))) → ((p4 → p2) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152734488939668124020538920760 : (((p5 ∨ True) ∨ (((p2 ∧ False) ∧ p2) ∨ ((True ∨ (((True ∧ p1) → p4) ∧ p4)) ∨ (True → (p1 → p3))))) → (p2 ∨ (p5 → (True → True)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60716172944193967308122288645 : ((True ∧ ((((p3 ∨ p5) ∧ True) ∨ (p5 ∧ p2)) ∨ (True → ((((p3 → True) ∨ p2) ∧ True) ∧ ((True ∧ (p4 ∨ (p5 ∨ p4))) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134347686925380908249493435757 : (((p5 ∧ (p2 ∨ (p5 ∨ ((p2 ∧ False) ∨ (False → (((p3 → p5) ∧ (True ∧ True)) → (p1 ∨ (p1 ∨ True)))))))) ∨ p1) ∨ (p5 → (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177655839954692787710250787948 : ((((((p3 → p1) ∨ (p1 ∧ p2)) → (False ∨ (p3 ∨ True))) ∨ True) ∧ p2) ∨ (False → ((((p4 ∧ (p4 ∧ (p1 → False))) ∨ p1) → False) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172957982743884351242723980318 : ((p4 ∧ ((((p5 → (p2 → p4)) → (p4 ∨ (p3 ∧ (p4 → p2)))) ∨ p2) ∨ p4)) ∨ ((False ∧ True) → (((p4 ∨ p2) ∨ True) ∧ (False → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164998958703916027544627141457 : ((((((p1 → True) ∧ p5) ∧ ((True → p5) → p4)) ∨ ((False ∧ p2) → (p4 ∧ True))) → p1) ∨ (True → (True ∨ (((p2 ∨ p2) ∧ p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43460004302410103479061885139 : (((((p1 ∨ False) ∨ ((p4 → ((p4 ∨ p2) ∨ p1)) ∨ (p2 ∧ ((p4 ∨ p3) → ((((p2 → True) ∨ p4) ∧ p1) ∨ p4))))) ∨ p2) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134235692264799350736132215755 : (((((False ∧ (p1 ∨ p5)) ∧ p4) ∨ (((p4 ∨ ((p5 → (((False ∧ p1) → p2) ∧ p5)) ∧ p2)) ∨ p4) → p3)) ∨ p1) ∨ ((True ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232297042613879796925727243932 : (((p3 → True) → p5) → ((p1 → (((p3 → (((((p4 ∨ p3) → (p1 ∧ False)) ∨ p4) ∨ p5) ∨ p5)) ∧ (p1 ∨ p4)) → p5)) ∨ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h11
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258361605261594283443417985020 : ((p5 ∨ False) → (((p2 → ((p1 ∧ (True ∧ (p1 ∨ p2))) ∧ False)) → (p4 ∧ p3)) → ((False ∨ False) ∨ ((p4 → (p3 ∨ (p4 ∨ p3))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322608929283665190353785720717 : (p5 ∨ ((p3 → (p2 ∧ (p4 ∨ (p3 ∧ ((p2 → ((p3 ∨ (p4 ∨ (True ∨ (False ∧ (False → (p2 ∨ False)))))) → p5)) ∧ (p2 → False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172936629185298814325878047364 : ((p3 ∧ (((p2 → p4) ∨ ((p4 ∨ p1) ∨ (False ∧ p2))) ∧ ((p2 → p3) ∨ p1))) ∨ ((p3 ∧ p4) → (((p3 ∨ (p3 ∧ p3)) → p4) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329286437102078742954369484113 : (True → (((p1 → p5) → p3) ∨ ((True → (((p1 ∨ (((True ∨ p5) → True) → (False ∧ p1))) → ((p3 ∧ p2) ∧ (p2 → p2))) ∧ False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48424986889698600863894024512 : (((p3 → (((p5 ∨ False) ∧ ((p2 ∧ False) ∨ (True → ((False ∨ p1) → True)))) ∨ ((True → False) ∧ (False ∨ (p1 → False))))) → (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158525700696599622622192978185 : (((p5 ∨ False) → ((True ∧ (False ∨ p2)) ∧ (((p4 ∨ p2) ∧ (p3 ∧ (p1 ∧ (p5 → p5)))) ∨ p1))) ∨ (p5 → (p5 ∨ ((p5 → True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184772493165196230527008576787 : (((((False → False) ∧ True) ∧ p1) ∨ (p3 ∧ ((False ∧ True) ∧ p5))) ∨ (((((p3 → p4) ∧ (p3 → ((False ∨ True) → True))) ∧ p1) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593426312335925962812549952349 : (((((((True ∨ (((False → (p1 ∨ False)) → p3) → p4)) → ((p5 → p2) ∧ p4)) → ((True ∧ p1) ∧ True)) → (p2 → (p3 ∨ p2))) ∧ True) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299390229434772937769403975467 : (False ∨ ((True ∧ ((p3 ∨ ((p1 → ((((p4 ∨ p3) ∧ (p4 ∨ p4)) → p3) ∨ (False ∧ (p5 ∧ True)))) ∨ p5)) ∧ ((False ∨ p5) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60491688048373215824527783523 : ((True ∧ ((((p1 → p1) ∧ ((((p3 → p2) → (False → (((p5 ∧ p1) ∨ p5) → p5))) → (p3 → p4)) ∨ p5)) ∧ (p3 ∧ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159205770907220191887588947281 : ((p2 → ((((p4 → (False → p3)) → False) ∨ (p5 ∨ (p5 ∨ p3))) ∨ (True ∨ ((p2 ∧ p4) ∧ False)))) ∨ ((p2 → ((p1 → p4) → p4)) ∨ False)) := by
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
theorem thm_5_vars_596609996104478922406693640529 : ((((((((p5 ∧ p1) → p4) ∧ p5) ∧ False) ∧ (((p2 ∨ p5) → (((p4 ∨ (p4 ∧ True)) → p1) → (p1 ∧ (p4 → p5)))) → p2)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67586235500688218093571583883 : ((p1 → ((p1 → False) → ((p4 ∨ False) ∧ ((((p3 ∨ ((False ∧ (True ∧ False)) ∨ (p3 ∨ p3))) ∧ ((p5 ∧ p1) ∧ p1)) ∨ False) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226609753081152703260700398081 : (((p5 → p3) ∨ p2) ∨ (((False ∧ (((p5 → (p2 ∨ ((p4 ∧ p1) → p1))) → False) → False)) ∨ p4) ∨ ((p5 → (p2 ∨ (p5 ∨ p3))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249130720372040662774215610216 : ((p4 ∨ p2) ∨ (((p2 ∨ ((p5 → (p5 ∧ p2)) → p2)) → (p4 ∧ (False → p5))) → (p1 ∨ ((((False → p2) ∨ (False ∨ False)) → p5) ∨ True)))) := by
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
theorem thm_5_vars_901443846893447677332822025017 : ((((((False ∨ (((p4 ∨ ((p4 ∧ p3) → p2)) ∧ ((p1 ∧ p1) → p5)) ∨ (p3 ∧ p4))) → p3) ∧ p2) ∧ (p1 → (p2 ∧ (p4 → p3)))) → p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43673132062650218373790061706 : (((((True ∧ (((((p2 → False) → False) ∨ (p4 ∨ (True ∧ True))) ∨ p2) ∧ p2)) ∨ (p5 ∨ ((False ∧ (p3 → p1)) ∧ p3))) → p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160327112168384549623001844584 : ((((True ∨ p5) → ((p5 ∨ p5) → (p4 ∧ (p4 ∧ (p5 → ((p3 ∧ p1) ∨ p4)))))) → (p2 ∨ p3)) → ((((p1 ∧ p1) → False) ∧ p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932169660022582595740557607722 : (((((p5 → (p4 → ((p2 ∨ True) ∧ p5))) → p1) ∧ ((p2 ∧ (False ∧ (p2 → p1))) → (p4 ∨ (True → (True ∧ ((p5 ∨ p4) ∧ p2)))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p4 → ((p2 ∨ True) ∧ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745674986799464378540587596949 : ((((True ∨ p4) → (((p1 ∧ (p4 ∨ (True ∨ (((p2 ∨ False) ∧ p1) → (p1 → ((p3 ∨ False) → (p3 ∧ p1))))))) ∨ p3) ∨ (True ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669934929592297044818392736857 : (((((False → (p3 ∨ (True ∨ ((p5 ∨ (p1 ∨ False)) ∨ p5)))) ∧ (False ∧ (p2 ∨ (p2 ∨ ((p4 ∨ p1) ∧ p3))))) ∨ ((False ∨ p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323656032692296268158096173465 : (p5 ∨ ((((True ∨ ((((p4 ∨ p3) ∧ p5) → ((p5 ∧ p3) ∨ True)) ∨ (False ∧ (p1 ∧ p2)))) → p2) → p3) ∨ (p1 → ((p2 ∨ p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41126874311738589837526699272 : (((((p2 ∨ ((p2 ∧ (((False ∧ (p1 ∨ p5)) ∧ (False ∨ False)) → p1)) ∧ (False ∧ (True ∨ False)))) ∧ False) ∨ (p3 ∨ (p1 ∨ p4))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602817800696977520068044475236 : ((((p1 ∨ (((((p5 ∨ (True ∧ (True → p5))) → (p4 ∨ p5)) ∧ (p3 → ((p4 ∧ (p5 ∧ p4)) ∧ p5))) → (p5 ∧ p5)) ∧ p2)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56335748808956362880036776314 : (((((False ∧ False) ∨ p1) ∨ p2) → (((p5 ∧ ((False ∧ True) ∨ (((p4 → p4) ∧ p4) → (((p5 → p1) ∧ p1) ∨ p4)))) ∧ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133709801378114426494518534633 : ((((p5 ∨ ((((False ∧ p4) ∨ (p3 → ((p5 ∧ False) ∧ False))) ∨ p3) ∧ p1)) ∨ (p1 ∧ ((p5 ∧ p4) ∧ p3))) ∧ p3) ∨ (False ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633559933918531657573670644741 : ((((((p4 ∧ (((p2 ∧ p2) ∨ p1) ∧ True)) ∧ (p3 → ((((p5 → False) ∧ p5) ∨ p2) → (p5 → (False ∨ p3))))) ∨ (p1 ∨ p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592534840432815601242808661943 : ((((((False → p2) → (((p1 ∧ p1) ∧ True) → ((((p4 → (True ∨ (p3 ∨ (False ∧ p5)))) ∧ p5) ∧ p5) → p4))) → (p1 ∧ p4)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147380950969616471810220461485 : ((((((p4 → p2) ∨ (False ∧ (True → p2))) ∨ (p3 ∧ p4)) ∨ ((p3 ∨ ((p1 ∨ p2) ∧ p5)) → False)) ∨ p4) ∨ ((p1 → (False → p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157554845189658370352249724536 : ((((((((False → (p4 ∨ p2)) ∨ p2) ∨ (p4 ∧ p5)) ∨ p4) ∨ p5) → (p5 ∨ True)) → (p5 ∨ p2)) ∨ ((p5 → (p5 ∨ False)) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324715633490806945554740875292 : (p5 ∨ (((p3 ∨ p2) ∨ p1) → (p4 → ((p5 ∧ ((p4 → ((False ∨ (p3 → (p5 ∧ (p5 ∨ (p3 → p4))))) → False)) ∧ (False → True))) → p3)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (False ∨ (p3 → (p5 ∧ (p5 ∨ (p3 → p4))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h13
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h17 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h18 := h6 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (False ∨ (p3 → (p5 ∧ (p5 ∨ (p3 → p4))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h19
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358036912853268970772075599155 : (p5 → (p1 ∨ ((p4 ∧ ((((p3 → ((False ∨ p2) → p1)) ∧ (p3 ∧ (p3 ∧ ((True ∧ (p4 ∧ p1)) → (True → p4))))) → False) ∧ p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165889241471624828613187204608 : ((((False ∨ p4) → p2) → ((((False ∧ ((p1 ∨ p5) ∨ p3)) ∧ p5) ∧ False) ∨ (p3 ∨ p4))) ∨ ((False ∧ p1) → ((p5 ∧ False) ∧ (p1 ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69392907224476337433979462352 : ((p5 → (p3 → ((((p4 ∧ (True ∨ True)) ∧ ((False → (p3 ∨ p5)) ∨ p5)) ∧ (False ∨ p5)) ∨ (p2 ∨ ((p1 ∨ p2) ∨ (p2 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59770569533564149950294289647 : (((p1 ∧ p5) → (False ∨ (True → (((((p4 → True) ∨ False) → (p3 ∨ p3)) ∨ True) ∨ (((p5 ∨ p1) → (p1 ∨ p4)) ∧ (False ∧ p2)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256915212568648104807134567651 : ((p1 ∨ p4) → ((p5 ∧ p5) ∨ ((((p5 ∧ (p1 ∨ p5)) ∧ (p2 ∧ (False → ((p2 ∧ p2) ∨ True)))) → (p4 ∨ (p2 ∧ False))) ∨ (False → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138204994339396134880657076471 : ((p1 → (p5 → (p1 → (p4 ∨ (((((((p4 ∧ (p5 ∨ p2)) ∧ p5) → False) → p4) ∨ (p2 ∧ p1)) ∧ True) ∧ p1))))) ∨ (True ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312336853590208165727745930514 : (p2 ∨ (p2 → (p5 ∨ (((p5 ∧ p3) ∨ ((p3 → (((True ∧ p3) → p2) ∧ (False ∧ ((False → True) ∧ p5)))) ∧ p3)) → (False ∨ (p4 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160804691110337679391141704052 : (((False ∨ (((p5 → p1) ∨ p5) ∧ p5)) ∨ ((((p4 → p2) → ((p4 → p4) ∧ p2)) → False) → p3)) → ((False ∨ p3) ∨ ((p3 ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153763945809900199097667710962 : ((p4 → ((p1 → (p1 → (False ∧ ((True ∨ p3) ∨ ((((p3 ∨ (p2 ∨ p2)) ∨ p4) → p5) → p2))))) → p3)) → ((p3 → False) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118603811699605076813046263807 : ((p4 ∨ ((((True ∧ p3) → p4) ∨ (((p3 ∧ (p3 → p2)) ∨ True) → ((p5 ∧ p5) ∨ (True → False)))) ∧ ((p4 ∨ True) ∨ p4))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178733707092224567821287058169 : ((((p4 ∧ p3) → (p1 ∧ False)) → (((p5 → p4) ∨ (True ∨ True)) ∧ p5)) ∨ (p1 → ((((True → p4) → (p1 ∨ (True ∨ p3))) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210094217927710421351702853412 : ((((p1 ∨ p3) ∧ p2) ∨ True) ∧ (p3 → (p1 → (p2 → ((((((p1 ∧ p4) → p4) → (p3 ∧ (p4 ∧ False))) ∨ (p1 ∧ p4)) ∧ True) → p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∧ p4) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h8
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327822746233387476494070049416 : (True → ((((p2 ∧ p5) ∧ ((False → True) → ((p2 ∧ (((p5 ∧ ((False → True) → True)) → p1) ∧ p5)) ∨ p2))) ∧ (p1 → p5)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179403969324802887794709560986 : ((p3 ∨ (p1 ∨ (((p4 ∧ ((p1 ∧ (p5 ∧ True)) → p4)) ∧ False) ∨ True))) ∨ (p4 ∨ ((p4 ∧ (True ∨ p3)) → ((p1 ∨ p5) → (p3 ∧ p4))))) := by
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
theorem thm_5_vars_304933953336229107732880899573 : (p1 ∨ (((((p3 → (p2 ∨ p4)) ∨ (p5 ∧ ((p5 ∧ ((p5 ∨ False) → p3)) → p4))) → p3) ∨ ((p2 ∧ p3) → p2)) ∧ ((p2 → True) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192556977268955213099439861875 : (((False ∨ (((p5 → p2) ∨ p3) ∨ (p4 → p2))) ∨ False) → ((p1 → (((p4 → False) ∨ True) → ((p2 ∨ p1) ∨ (p1 → (False → p1))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h7
          -- Implications on the right can always be decomposed.
          intro h8
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253645375482703208995913503870 : ((p1 ∧ True) → (False ∨ (((p5 ∨ p4) → False) → (True → (p1 ∧ (p1 ∧ (((((p4 → p3) ∧ False) ∨ p5) ∨ (p4 → (False ∧ p5))) ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112870807494643100928543065842 : (((((p2 ∧ p1) → False) → (((((p5 → True) ∧ p1) ∨ True) ∨ p2) ∧ (((p2 ∨ False) ∨ (p2 → p4)) ∨ (p4 ∧ False)))) → p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667127561186409243094843981753 : (((((p4 ∧ (True ∧ p3)) ∨ (((p5 ∨ (p3 ∨ (p4 → (False ∧ p1)))) → (True ∧ False)) ∧ (p4 → (True → p3)))) ∧ (p1 ∨ (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317614752477556389908435615913 : (p4 ∨ ((((((p3 ∨ (p4 ∧ p3)) ∧ p2) ∨ ((False ∨ (((p5 ∧ p4) → True) ∧ (p1 ∧ ((True ∧ False) ∧ p1)))) ∧ p1)) ∧ False) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310796051251909018095630492124 : (p2 ∨ (((p5 → p1) → p3) ∨ ((p1 → (True → p2)) ∨ (p1 ∨ ((True ∧ (True ∨ p3)) ∨ (False ∧ (p5 ∨ (True → (p1 ∧ (False ∨ p3)))))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185207153765049177622190669268 : ((True ∧ (p1 ∧ ((p3 ∧ (p5 ∨ True)) → ((p2 → True) → p5)))) ∨ ((p3 ∨ (p5 ∧ (p2 ∧ ((p1 ∧ False) ∨ True)))) ∨ ((True ∨ False) ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166314688023515904206701762486 : ((p5 ∧ ((p4 → ((((p5 ∧ (p3 ∨ (p4 ∨ p4))) ∨ (p5 ∨ p2)) ∨ True) ∨ p5)) ∨ False)) ∨ ((False → p1) ∧ ((True → p3) → (p4 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113631470004123230847569945236 : (((p3 → (False ∧ ((((p3 → (False ∨ ((p5 → p4) ∨ (p5 ∨ False)))) → (p1 ∧ p5)) → (p2 ∨ p1)) → False))) ∨ (p5 ∨ True)) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9122211124774903239442638266 : ((((p3 ∧ (p1 ∧ (True ∧ (p4 ∨ (((p4 ∧ True) ∨ p1) → False))))) ∨ (p5 ∨ (((p2 ∨ (True ∧ False)) → p1) → (p1 ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115898803870937579816502357410 : (((((True ∧ p5) → p5) → p5) ∨ (((p2 ∧ ((p1 → (p5 ∧ p5)) → False)) ∨ (p2 → p1)) ∨ (p3 ∨ (p5 ∧ (p5 ∨ p1))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707008128948101252161118767643 : (((((p4 ∧ (p2 ∧ (False ∧ (p1 → p2)))) ∨ p2) ∨ (((False ∨ p3) ∧ (True ∨ (True → (p5 ∧ p3)))) → (((p3 → True) → p3) → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263901944429688348310971108595 : (True ∧ ((p2 ∧ (False → ((((((p4 ∨ True) ∧ p2) → p5) ∨ p2) ∨ p1) ∨ True))) ∨ ((p2 → p3) → (p5 ∨ ((p4 → p5) ∨ (p1 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719595820630262098045045255922 : ((((p4 ∨ (p3 ∨ (p5 ∧ p3))) ∨ (p3 → (((((p2 → p5) → p2) ∧ (p3 ∨ ((p1 → (p5 ∧ p2)) ∨ p3))) ∧ p5) → (True → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



