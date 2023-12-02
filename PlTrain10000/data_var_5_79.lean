variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143022794773582850030344262314 : ((True → (p2 ∨ (((((False ∨ ((True → (p3 → True)) ∧ (p3 ∧ p5))) ∨ p5) → p1) → ((p5 → p3) ∧ p1)) → False))) → (p4 → (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599777346897099863794293587393 : (((((p5 → p2) ∨ (False ∨ ((p1 ∨ ((p1 → p3) ∨ False)) ∧ (((True ∧ p5) ∧ (p5 ∨ p3)) ∧ (p4 ∨ (p3 ∧ (p1 ∨ p2))))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196722366025237173264480525944 : (((((p5 ∧ False) ∨ (False ∨ p5)) → False) ∧ p5) ∨ ((((p3 ∧ (True ∧ (False → ((True ∧ p5) ∧ (True ∨ p3))))) ∧ p3) ∨ p4) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608849843949241869572458020335 : (((((((((((p1 → p1) → p4) → (p2 ∧ p2)) ∨ p5) ∨ ((p5 ∧ True) ∧ True)) → p1) ∨ ((p3 ∨ p4) ∨ (True → p4))) ∨ p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657135732960209343389442820143 : ((((((False → p4) → p2) ∨ ((p2 → (((p2 ∨ p3) ∨ p1) → (((True ∧ True) ∧ (False ∨ p3)) ∧ p3))) ∧ (p5 ∧ p2))) ∨ (p3 → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_342883518276384119615884328798 : (p2 → ((((p3 ∨ p5) → (p3 ∨ p5)) ∧ p4) → ((((False ∧ (p5 ∨ (False ∧ ((False ∨ True) → (False ∧ p4))))) ∧ (p1 → p5)) ∨ True) ∨ p2))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245054205052905650346148206177 : ((p1 ∧ p5) ∨ (((((((True → (p5 ∧ (p3 → ((p5 ∧ p5) → True)))) ∨ p1) ∨ p5) ∨ p2) ∨ (p4 → p5)) ∧ p5) ∨ ((p1 ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158281037637946544252236873183 : (((p5 → (p1 ∧ p1)) ∨ ((True ∧ ((True ∨ ((((p4 ∧ True) ∨ p2) ∧ p2) ∧ p1)) → p1)) → p5)) ∨ ((((p4 → True) ∨ p4) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356141363794558885645436481399 : (p5 → (((True → ((True → p4) → ((p2 → ((False → p3) → ((p4 → p2) → p4))) → p2))) ∧ True) ∨ (p2 ∨ (False → ((False → p1) → True))))) := by
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
theorem thm_5_vars_208931417258265611824595477818 : ((p5 ∧ (p1 ∨ ((p1 → False) ∨ p4))) → ((((p2 ∨ ((p3 ∧ (p4 → (p2 → ((p1 ∨ False) ∧ p5)))) → (p2 ∨ p2))) ∧ p4) ∧ p5) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112064653328918092384077782608 : ((((p4 ∨ True) ∧ ((((p2 ∨ ((p4 → p1) ∧ False)) → p2) → (p4 ∨ (p2 → ((p1 → (p1 → p3)) ∨ False)))) ∧ p4)) ∨ p4) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585685590858153426593849157926 : (((((((((False ∨ p1) → (p1 → (((False ∧ p4) ∨ (p2 ∨ p1)) ∨ (p1 ∨ p1)))) ∨ ((False ∧ False) ∧ p2)) → p1) → False) ∧ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187306744040037732872587328164 : ((p1 ∧ ((p2 → ((p3 → p5) ∨ p5)) ∧ ((p4 → True) ∨ p3))) → ((((((True ∨ True) ∧ True) ∧ p1) ∨ p4) ∨ p3) → ((p1 → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h1.left
        let h12 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h16 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h17 := h3 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h25 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h26 := h3 h25
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h1.left
      let h30 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h34 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h35 := h3 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h1.left
    let h39 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h43 =>
      -- One of the premise coincides with the conclusion.
      exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55297374208222573491253736918 : (((p3 ∧ (p4 → ((p2 ∧ p1) ∧ p3))) ∨ ((False ∨ ((p3 ∧ p4) → ((p3 → (p2 → p5)) ∨ ((True → p3) ∧ p4)))) → (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52219037891970877286736703080 : ((((p2 ∨ True) → ((p5 → (False ∨ ((p1 ∨ p4) → p2))) → (p1 ∧ (p2 → False)))) → ((((p2 → False) → p5) ∨ (p4 ∧ p5)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638353349532772337240704822139 : (((((((p1 → p4) → False) → (p2 ∧ p5)) ∧ (p2 ∧ ((((p5 → False) → p2) ∨ True) → (p1 ∧ (False ∨ (p5 ∧ (False ∨ p1))))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58595293572071090115428559142 : (((False → True) ∧ (False ∨ (((p1 → (p5 ∨ (p2 ∨ p1))) ∧ ((((p1 ∨ p1) → p4) → ((True ∧ p1) ∨ p5)) ∨ True)) ∨ (p5 ∧ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618286994841821926269873826462 : ((((((p2 → p5) ∧ (True ∨ False)) ∨ (p4 ∧ (((p1 ∧ p2) ∧ p1) ∨ (((False ∨ True) → (p3 ∧ (p2 → (p3 → p1)))) → p2)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249293205681244171664520657951 : ((p4 ∨ p5) ∨ ((p2 ∨ ((((p2 ∧ (p2 ∧ p4)) ∧ p4) → (((p1 ∧ p1) ∨ True) ∧ (((p5 → p5) ∨ (False → p5)) ∧ p5))) ∨ True)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140646449596507209262033807401 : ((((((True → p3) ∨ (p4 ∨ (p3 ∨ (p1 ∧ (p1 ∧ p1))))) ∧ True) → p1) ∧ (((True → (p3 → p3)) → p1) → p1)) → ((p3 → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300106270009649507704273605849 : (False ∨ (((((p2 ∨ (p3 → p2)) ∨ ((p4 ∨ p4) → (p5 ∨ True))) ∨ p4) → (p2 ∨ ((((p4 → p3) → p4) → p2) ∨ p5))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54906170469059437226734500563 : ((((p3 → ((p5 → True) ∨ p5)) ∨ p3) ∧ ((p5 ∨ (((p1 ∨ (((p5 ∧ p4) → p2) → (True ∨ True))) ∧ p4) ∨ p4)) ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644109664444931060855389819587 : ((((True ∨ ((True ∧ p3) → ((False → (p3 → p3)) ∧ ((p1 → (False → ((p1 ∧ p4) → (p1 ∧ (p5 ∨ (True ∨ p1)))))) ∨ True)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148563011591547842301193404036 : ((((p5 → p2) ∧ ((p5 → p3) → (p3 ∧ (p2 ∨ p5)))) ∧ ((((False ∨ False) ∧ True) → (False → True)) ∧ p4)) ∨ ((p5 ∨ (p4 → p4)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174564092986264962998026110287 : ((((False ∨ p2) ∨ (True ∧ p2)) ∧ (False ∨ (((False ∨ False) → (p4 ∧ False)) ∧ p5))) → (p4 ∨ ((False ∧ p2) ∨ (((p2 → p5) → p3) → p3)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : (p2 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h14 := h11 h12
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p2 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h25 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204562221038194437724830764975 : ((((p1 ∧ p3) ∧ (p3 → True)) ∨ p2) ∨ (((p2 → (False ∨ ((p3 ∧ p2) → (p1 ∧ (p3 ∧ p4))))) ∨ ((p1 → p2) → (p2 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598696618713850383072012166843 : (((((p4 → (p5 ∧ p2)) → ((False ∨ p3) → ((p2 ∧ (p5 ∧ ((p2 ∨ p5) ∨ ((p2 ∨ (p3 ∨ (p3 → p4))) → p4)))) ∨ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147450556090894292665717644149 : ((((p1 → p2) ∨ ((p2 ∧ ((p3 ∧ (p2 → p3)) ∨ ((p2 ∨ p4) ∧ p1))) ∨ ((False ∧ False) → p4))) ∨ p1) ∨ (False ∨ ((False ∧ p2) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_766036116952502304018196758007 : (((p4 ∧ (((p1 ∨ p5) ∧ p3) ∨ ((((p5 → p2) → (p1 ∧ p2)) → p3) ∧ ((((p3 ∧ p4) ∨ (p3 ∨ True)) ∧ (p5 ∧ p5)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322314169470237727199030413275 : (p5 ∨ (((p5 → (((True → (((False → p1) ∨ p2) → (p3 ∨ p1))) ∧ p5) → (((p5 ∨ p1) → p3) → (p1 → (False → p3))))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114218167526483426458996300681 : ((((False ∧ p4) ∨ (p2 → (((((True ∨ p3) ∨ p1) → (p5 ∨ p5)) ∨ p4) ∨ ((p4 → p3) ∧ p1)))) → (p3 → (p4 ∧ True))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147393850767523951212130310664 : (((((((True → (p4 ∧ False)) → False) ∨ p5) → True) → ((((p2 ∧ p5) ∧ p3) → p5) ∧ (p4 ∧ p5))) ∨ p1) ∨ (False ∨ (True → (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265662967782634248737649998989 : (True ∧ (p2 ∨ ((False ∨ (False ∨ (p3 → True))) → (((p4 ∨ (p1 → (p5 ∧ (False ∨ p1)))) ∨ ((p4 ∧ False) ∧ (p5 → p1))) ∨ (p1 → p1))))) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807981116341361151556320085279 : (((p4 → ((p4 ∨ p3) → ((((p4 ∨ ((p2 ∨ False) ∧ p5)) ∧ p3) → (False ∧ (p2 ∨ ((p3 ∧ p1) → (p3 ∧ True))))) → (p3 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307375407602797750559231735546 : (p1 ∨ (p4 ∨ ((True → ((False ∨ ((p4 ∨ ((p2 ∨ (True ∨ ((p4 → (p1 ∨ p5)) → (False ∨ p2)))) → p2)) → p4)) ∨ p2)) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_52989518201769567700627034690 : ((((((p4 → p3) ∧ (True ∧ (True ∧ True))) ∧ p4) ∨ (p5 ∨ p1)) ∧ (True ∧ (((p4 → (p4 ∧ p1)) ∧ p5) ∧ (p2 ∧ (p3 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133227107399414678967987814129 : ((p1 → (True ∧ (((((p1 ∧ (((p3 ∨ p4) → False) ∧ p3)) ∧ (p4 ∨ p4)) ∧ p1) ∧ p4) ∨ (p2 → (p4 ∨ p2))))) ∧ (p1 ∨ (False → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701655287654661817577107559755 : (((((p1 ∧ True) → ((False → (p3 → False)) → (p2 ∨ False))) ∧ ((p4 → (p2 ∧ ((((p5 → p4) → p4) ∧ p2) ∧ p2))) ∨ (p5 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109764793696952360152866345068 : ((p5 ∨ ((((p3 ∨ (True ∨ (p3 ∨ (p1 → (p1 ∨ p1))))) → ((((True → (p4 ∨ p2)) ∨ True) ∧ p4) → p4)) → p1) ∨ True)) ∧ (False → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737991414786606019185915904926 : ((((True ∧ p5) ∨ ((((((p3 ∧ p5) ∧ p5) ∨ p4) → (p4 ∨ (p3 → (p2 → (((p3 → p4) ∧ p5) → (True ∧ False)))))) ∨ False) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_53906339914569640795597311465 : (((p5 ∧ ((p5 ∧ (p4 → ((False ∧ p5) ∨ False))) ∧ p1)) ∨ ((False ∨ ((p1 ∨ p2) ∧ False)) ∨ (((p2 → p5) ∧ False) → (False ∧ False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53236693327219576750036838237 : ((((p3 → (True ∧ p2)) ∧ (p4 ∧ ((p3 ∧ p4) → (False ∨ True)))) ∨ ((p5 → True) → ((p5 ∧ True) ∨ (p5 → (False ∨ (p2 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65740375483974635070528354785 : ((p4 ∨ (((p4 ∨ (p5 → (((((p5 ∧ p4) → True) ∨ ((p4 → (p1 ∨ p5)) ∧ p5)) ∧ p5) → p1))) → False) ∨ ((True ∨ False) ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_200990418885264085812490093599 : ((p3 ∨ (((False ∧ (p4 ∧ p5)) ∨ p2) → p5)) → (p3 ∨ (((((p4 → p3) ∧ (p2 ∧ (p3 ∧ False))) ∧ p1) ∨ True) ∧ (True ∨ (p5 ∧ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49701011431336490811317720450 : ((((p3 ∧ p1) → (p1 → ((p4 ∨ (p4 ∨ p3)) ∧ ((((p2 ∧ p1) → ((p3 ∧ p5) → p5)) ∧ False) ∧ p4)))) → ((True ∨ p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151086270980523432681620584221 : ((((True → (p1 ∧ ((((True ∨ True) ∧ (p4 → ((p1 ∧ True) ∨ p5))) ∧ p2) ∨ (p1 ∧ p5)))) ∨ p2) → p3) → (p3 → ((p4 ∨ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2365290151468732286063352969 : ((((True ∧ ((((p5 → p5) ∨ p1) → p3) ∧ p5)) → p5) → p3) ∨ (((p2 ∧ False) ∧ (p2 ∨ p3)) ∨ (p5 → (p5 ∨ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53611255579001456937330983493 : (((((False ∨ (False ∨ False)) ∨ (p2 ∧ p5)) ∨ (p4 → p4)) ∧ (((True → p4) ∧ ((p1 → ((True ∨ p1) ∧ p1)) ∨ (p4 ∧ False))) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243946715753513837588522227376 : ((True ∧ p1) ∨ ((((p5 → ((p4 ∨ (p5 ∧ False)) ∨ False)) ∧ (p2 ∧ (p5 ∧ (False → p1)))) ∨ (p1 ∨ (True ∧ ((p5 ∧ True) ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229047407811494898481114624043 : ((p5 ∨ (p2 ∨ p5)) ∨ (p5 → (((True ∨ (((p5 ∧ (p3 → (p4 ∧ ((True ∧ (p3 ∨ p1)) ∧ (p1 ∨ p5))))) ∨ True) → p4)) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156955267798603834628379603924 : ((((p1 → ((p4 → (((p5 → p1) → p5) ∨ (p3 ∧ p4))) → False)) ∧ (p2 ∨ (True ∧ p3))) ∨ p5) ∨ ((True ∨ p5) ∨ (True → (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51957652972847312273164558877 : (((((p2 → (True → p4)) → p2) ∨ (p2 → (False ∧ ((p1 ∧ (True ∨ p4)) → p3)))) ∨ ((p5 ∧ (((p5 ∧ p3) → p2) ∧ p3)) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655957802730033651156983720998 : (((((p5 ∨ ((p4 ∧ (p1 ∧ ((p4 → True) ∧ (p5 ∧ ((p2 → p1) ∨ p1))))) ∨ True)) ∧ ((True ∨ (p5 ∨ p1)) ∨ p5)) ∨ (p3 ∧ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47497370468145391798634221212 : (((p1 ∨ (((p2 ∧ (False → (p4 → (p4 → (p2 → (p4 ∨ True)))))) ∧ (p2 ∨ (p4 → (p2 ∧ False)))) ∧ (p2 ∨ p1))) ∨ (False → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314956081686670158299487520192 : (p3 ∨ (((True ∨ (p1 → p5)) ∧ (p4 ∨ ((True ∧ p5) → True))) → ((p3 ∨ (False → ((p3 ∨ ((p3 ∧ p2) ∧ p1)) → True))) ∨ (False → True)))) := by
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
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950361298898145497150171955732 : (((((p4 → p4) → False) ∧ ((p4 ∧ p3) ∨ ((False ∨ True) → ((((p2 → False) ∨ False) ∧ (False ∧ (False ∨ (p4 → p1)))) → (p1 ∨ p4))))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172875545433940616227008668806 : ((p1 ∧ ((((((False ∧ False) → p4) → (p5 ∨ p4)) ∨ False) → False) → (False → p4))) ∨ (True ∧ ((False ∨ p2) ∨ (p3 → (p1 ∨ (False ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720970698409776715687889758957 : (((((p5 ∨ p4) ∧ (p3 ∨ p4)) → (((p2 ∧ ((p3 ∨ p3) ∨ True)) ∧ (p5 → (p5 → (((p1 ∧ (True → False)) → p4) ∨ p3)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638899694659811734009625756495 : ((((((p3 → p2) ∧ (p3 → p2)) ∧ (((p5 ∨ (False ∨ p2)) ∧ (p5 → (((p1 ∧ (p1 ∧ p3)) → p4) ∧ p1))) ∧ (p3 ∧ p5))) → p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h7.left
      let h20 := h7.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h22 := h9 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174494134722467626539550701472 : ((((p3 ∨ (p2 → (p1 → p1))) ∧ p5) ∨ (p2 ∨ (p4 ∨ (p2 ∧ (False ∨ True))))) → (p5 ∨ ((p5 ∧ p2) ∨ (False → (p3 ∨ (p3 ∧ p1)))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594083936001948151090486350748 : ((((((p1 → (p4 → ((p3 ∧ (((p3 ∨ p2) ∨ ((p3 ∧ p4) ∧ True)) ∨ p5)) → p3))) ∨ p5) → ((p2 ∧ (p1 ∧ True)) → False)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323913384130603029585120022846 : (p5 ∨ ((True → ((((p1 ∨ (((p3 ∧ p1) → p3) → p1)) ∧ p3) ∧ p3) ∨ (False ∨ True))) ∨ ((p1 ∧ p1) → (p2 → (p4 → (p4 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324483234019491385537007083008 : (p5 ∨ (((p5 ∧ (p1 → False)) ∨ p5) ∨ (((p1 ∨ p3) ∨ True) ∨ ((((True → (True ∨ (((p1 ∧ p1) → True) ∧ p1))) ∧ False) ∨ False) ∨ p2)))) := by
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
theorem thm_5_vars_47603045671939799837891740147 : (((p3 → (p4 ∨ ((p5 ∨ ((((False ∧ (p1 ∧ False)) ∧ p4) → ((p2 ∨ ((p1 ∨ p4) ∨ p3)) ∨ p5)) ∧ p1)) → p2))) ∨ (False → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781081548781148831134432636283 : (((p2 ∨ ((False ∧ p2) ∨ (p1 → (((p1 ∨ (p4 ∨ ((p5 → p3) → p3))) ∧ (p2 ∨ p2)) ∨ (p1 ∨ ((False ∨ p2) ∧ (p1 ∧ p2))))))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227063337177072106412132084402 : (((p3 ∨ False) → False) ∨ (((((p4 ∧ ((((p1 ∨ (p1 ∧ p2)) ∨ False) ∧ False) ∨ True)) ∨ (False ∧ p1)) ∧ ((p1 → p2) ∨ p3)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327982301138240395573483764673 : (True → (((p4 ∧ p3) ∧ ((p3 ∨ (p3 ∨ True)) ∨ (((p3 ∨ (False → (p4 → p5))) ∧ (p1 ∧ (True ∧ p1))) ∧ (p5 ∨ p1)))) → (False ∨ p3))) := by
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
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
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
      -- Conjunctions on the left can always be decomposed.
      let h25 := h16.left
      let h26 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336343133923897196099862798871 : (p1 → (((True ∨ True) ∧ ((((((p4 → (True ∨ p3)) → p2) ∨ (((p5 ∧ True) → (p3 ∧ p5)) → p3)) ∧ p5) → (p4 ∧ True)) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_245086257940001118015831374681 : ((p1 ∧ p5) ∨ (p5 ∨ (((False ∧ False) ∧ (True ∧ (p2 ∧ (True ∨ ((p4 ∧ (True → ((p2 ∨ p3) ∧ (p3 → False)))) ∨ False))))) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_861192179935023847524884839807 : (((((((((p2 → p5) → ((True ∨ p2) → (p4 ∧ ((False ∧ True) → (p5 ∨ True))))) ∧ p1) → p2) ∧ p2) ∨ ((p5 → True) ∧ True)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p2 → p5) → ((True ∨ p2) → (p4 ∧ ((False ∧ True) → (p5 ∨ True))))) ∧ p1) → p2) ∧ p2) ∨ ((p5 → True) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354979679939107069587082826015 : (p5 → ((p5 → (((((p1 ∧ (p3 ∧ ((True ∨ p5) ∨ p5))) → (False ∧ p4)) ∨ p2) ∨ p3) ∨ (p1 → (((p2 ∨ p5) ∨ p2) ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196665245379556143632854736213 : ((((p1 ∧ (p2 ∨ (True → p2))) ∧ True) ∧ True) ∨ (p3 ∨ (((p3 → ((True ∧ False) ∨ (p3 ∨ True))) ∨ ((p4 ∨ p4) ∧ (p3 ∧ p1))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791461827815813641467846541536 : (((True → ((False ∧ ((p3 ∧ ((p2 → p1) → (p2 ∧ (((p4 ∧ (True ∧ p5)) ∧ p2) → (p3 → (False ∨ (p4 ∧ p2))))))) ∧ p4)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_299192076438504060582339098005 : (False ∨ (((True ∨ ((((((p4 → p5) ∧ True) ∨ p5) ∨ True) ∨ (((p1 → p5) → True) ∨ p5)) ∨ ((p3 ∧ p2) ∧ (p1 → True)))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179870805908799279215287673983 : (((p3 → (True → (((p4 → (False → False)) ∧ (p5 ∧ p4)) ∧ p3))) ∧ p1) → (((True ∨ (((True → True) ∨ False) ∧ p3)) → (p2 ∧ p3)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (((True → True) ∨ False) ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252936283349100422285352787739 : ((True ∧ p2) → ((True ∧ (p2 ∧ ((p1 ∧ (p4 → p5)) → ((((p3 ∨ ((p4 ∧ (p2 ∧ p3)) ∧ p1)) → p4) ∧ (False ∧ False)) ∨ p1)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122020367178782355547555969982 : (((p5 ∨ (((((False ∧ (p1 ∧ False)) ∨ p1) ∨ p4) → False) ∨ (p1 → ((False ∧ (p4 ∨ (p5 ∧ False))) → (p2 ∨ p1))))) → False) → (p5 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((((False ∧ (p1 ∧ False)) ∨ p1) ∨ p4) → False) ∨ (p1 → ((False ∧ (p4 ∨ (p5 ∧ False))) → (p2 ∨ p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113149184244890268723035360305 : (((p3 → ((p3 ∧ (p4 ∨ True)) ∧ ((((((False → (True ∨ (True ∧ False))) → p3) ∧ p3) → p4) ∨ (p2 ∨ True)) ∧ p3))) → p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703547476165795571945857196464 : ((((p1 → (p3 ∨ ((((p4 → p2) → p4) ∧ p3) ∧ p3))) ∨ (False → ((p5 → (p5 ∨ (False → p3))) ∨ (p1 ∧ ((p3 → p1) ∧ p3))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181077370602731800539409073263 : (((p3 ∨ p2) → (p1 ∧ (True ∨ (((p2 → p1) ∨ (p5 ∨ p4)) ∨ False)))) → (p4 → ((p2 → ((p5 ∨ (p2 ∧ (p2 ∧ p3))) → p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152646342430920708320583976860 : (((True → False) ∧ (False → (((False ∧ ((True ∧ (True ∧ ((p4 ∧ True) ∧ p3))) ∧ p1)) ∨ p2) ∨ (True ∧ False)))) → (p5 ∧ ((True ∧ p4) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346773387606961998468799693103 : (p3 → (((p1 ∧ ((True → True) ∨ ((((((p2 → p1) ∧ (p4 → p4)) ∧ p3) ∨ False) ∧ p2) ∨ p1))) → p4) ∨ ((p2 → (p2 ∨ p4)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149106147617490407387716293353 : (((p2 → (p2 ∧ True)) → (((p1 ∨ (p3 ∧ p4)) ∨ ((True ∧ ((p5 ∨ p2) → p4)) ∧ True)) ∨ (p2 → True))) ∨ (False → ((True ∨ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690153677270692518012874021802 : ((((p2 ∨ ((((p1 ∧ ((p1 ∧ (p5 → p1)) ∧ (p1 → p1))) → p2) ∨ True) ∧ p5)) ∨ (p1 → ((p1 ∨ True) ∨ ((p3 → p1) ∧ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116042854624215013481859848189 : (((p5 ∨ ((p4 → p4) ∨ p1)) → (((False ∧ (((False ∧ ((p3 ∧ p3) ∧ False)) → p5) ∧ p1)) → (p5 ∨ (p3 ∧ p5))) → p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4178964210266423239209793937 : (p4 ∨ ((p2 ∧ True) ∨ (((((p3 ∨ p5) ∨ p1) ∧ p3) → ((p3 ∧ False) ∨ ((True ∨ (p3 → p1)) ∨ False))) ∧ ((False ∧ p2) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47430380350625015159555644571 : (((p2 ∧ (((((((p5 ∧ p4) ∨ (((p4 ∨ True) → True) ∨ False)) ∨ p3) ∨ p3) ∧ (p4 ∧ p3)) ∧ (False → True)) → p1)) ∨ (True ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178422265360998341662756620228 : (((False → (((p1 ∧ p5) ∧ (p2 → (True ∨ p1))) ∧ p3)) → (p5 ∧ p2)) ∨ (((p4 → (True ∧ p1)) ∧ ((p3 ∨ p3) → p3)) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147506135157708527225260642701 : (((p2 ∨ (((((True ∧ ((p1 → True) ∧ p4)) ∧ ((True ∨ p4) → True)) → p3) ∧ (p2 ∨ p4)) ∧ p2)) ∨ True) ∨ (p2 ∨ ((p2 ∨ p3) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866712980524161813609991562684 : ((((((True ∨ p1) → False) → (((True ∧ p1) ∧ ((p1 → ((((p1 ∨ (False ∨ False)) ∨ (p1 ∨ p3)) → False) ∨ p3)) ∧ p4)) ∧ False)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p1) → False) → (((True ∧ p1) ∧ ((p1 → ((((p1 ∨ (False ∨ False)) ∨ (p1 ∨ p3)) → False) ∨ p3)) ∧ p4)) ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40433259231826014723196021992 : (((((False ∧ ((((p1 → False) ∨ p1) ∧ p2) → (False → True))) ∧ (True → (p5 ∧ ((p5 ∧ p5) → ((p5 → True) → False))))) ∨ p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111019554225954024325226482 : ((((p1 ∧ ((p2 ∨ p4) ∧ (((((False ∨ p1) ∨ p2) → True) → (False ∧ ((p3 → False) ∨ True))) → (p2 ∨ True)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620814465918548041466683507941 : (((((True ∨ p3) → ((((p4 ∨ (False → ((p4 ∨ True) ∧ (p5 → (p2 → p2))))) ∧ p1) ∧ (True ∧ (p4 ∨ (p3 ∧ p1)))) ∨ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119820240267916458202921202667 : (((((p3 → (True → (False ∧ (p3 ∧ p2)))) → (p5 → (((True → p1) ∧ p1) ∧ ((p4 ∨ (True ∨ p5)) ∨ False)))) → p4) ∧ p1) → (True ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → (True → (False ∧ (p3 ∧ p2)))) → (p5 → (((True → p1) ∧ p1) ∧ ((p4 ∨ (True ∨ p5)) ∨ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40780919165291088747916873249 : ((((p1 ∧ ((False ∧ p4) ∨ ((((p5 → True) ∨ (((((True ∨ False) → p1) → True) → p2) → p5)) ∧ p1) ∧ (p1 ∨ p4)))) → False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115343911872117156560751185713 : (((p1 → ((p3 ∧ (p5 ∧ ((True ∧ p1) ∨ p5))) ∨ False)) → (((p5 → p1) → p3) ∧ (p2 ∧ (p5 → (p5 ∨ (p2 ∧ p5)))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117645335793904695638700901229 : ((p3 ∧ (((False ∧ p5) → ((((p4 ∧ p5) ∨ ((False ∨ False) ∧ p2)) → ((p3 ∨ (p5 → p5)) ∧ (p4 ∧ p5))) ∧ p1)) → False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111565719804227817044684851595 : ((((((False ∧ p1) ∨ (True ∨ False)) ∧ ((p1 → (((p5 ∨ p1) ∧ ((True → True) ∧ p4)) → p2)) ∧ (p1 ∧ p1))) ∧ p1) ∨ p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599157618670286904089404228413 : (((((p2 → p2) ∧ (((p4 ∨ (((True ∨ p4) ∧ False) → (p5 ∨ p4))) → (p2 ∧ (p5 → (p2 ∨ ((p3 ∨ p3) ∨ False))))) ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622912741601557561434591038378 : ((((p5 ∧ ((((p2 ∨ False) → ((False ∧ (True ∧ (p5 ∨ p1))) ∨ ((p3 → p1) ∨ False))) ∧ (p5 ∨ p3)) ∧ (p5 ∧ (p2 → p3)))) ∨ True) ∨ p3) ∧ True) := by
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



