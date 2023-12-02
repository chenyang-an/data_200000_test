variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668709699558249498562816930611 : ((((((((True ∨ (((False ∧ (((p1 ∧ p2) ∧ p5) → False)) ∧ True) ∨ (p2 → True))) → p2) ∧ p4) ∨ p5) ∨ True) ∨ ((p3 ∧ False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116442058332992001623922123481 : (((p3 → (p1 → p1)) → ((p2 ∨ True) → (p2 ∧ (p2 ∨ (p2 ∧ (p5 → (((True → p5) ∧ p5) ∨ (p5 ∧ (False ∨ p4))))))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314761073321935906126861171540 : (p3 ∨ ((p2 → ((((((p3 ∨ p4) ∧ True) ∨ (p1 → True)) ∧ p5) ∧ p5) ∧ p3)) ∨ (p5 → ((p5 ∨ (p2 ∨ p4)) ∧ ((False ∨ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66172697791229244602585963541 : ((p5 ∨ ((((p5 ∨ (p4 → (((p5 ∨ p5) → p2) ∨ p3))) ∧ (p3 ∨ p2)) ∨ (((p3 → p4) ∨ p3) → p5)) → ((False → p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725587792864896880208255175987 : (((((p3 ∧ True) ∧ False) ∨ ((p4 → (p5 ∨ ((p3 ∨ ((((p1 ∧ ((False ∧ p3) ∨ p2)) ∨ p1) ∧ p1) → (p5 ∧ p3))) ∧ True))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_197462367639929243153882264603 : ((((p3 ∧ (True → p1)) → True) ∧ (False ∧ p3)) ∨ (True → ((p1 ∨ (False ∨ True)) → (True ∧ ((p4 → False) ∨ (False → (True → (p1 ∧ p1)))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166483908834794191831640830623 : ((p3 ∨ (((((p4 ∨ (p5 ∨ p4)) ∨ p4) ∧ False) ∨ (p2 → True)) ∨ ((False → True) ∧ p2))) ∨ (p4 ∨ ((p1 → p5) ∧ (p1 → (p3 → p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133591497493030837339848420071 : ((((p3 ∨ (((p5 ∨ (((False ∧ True) → (p3 → p3)) → p1)) ∧ p2) ∧ ((p1 ∨ p4) → (p3 ∨ p3)))) ∨ p5) ∧ False) ∨ (True → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752990883637182316296085593027 : (((False ∧ (((p2 ∨ ((p2 → p3) ∨ ((False ∨ p3) ∨ (p4 ∧ p2)))) → (((p3 ∧ (p2 ∨ True)) ∧ False) ∨ (p3 ∧ (p1 ∧ p5)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686911403677303682175017921817 : ((((False ∨ (p4 ∨ ((p5 ∨ ((p5 ∨ (p4 ∧ (((True ∨ p1) ∨ p3) ∨ p5))) → p4)) ∨ True))) → ((p1 ∧ (p4 ∧ p3)) ∨ (p2 → True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172797321003368132993123961458 : (((p3 → p3) → ((p1 → (p4 ∨ ((p1 → ((p4 ∧ p5) → False)) ∧ p4))) → p2)) ∨ (((p3 → p3) ∨ ((p2 → p2) ∨ (p4 → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180280995332484215830621093121 : (((p4 → ((((False ∨ (p3 ∨ (True ∨ True))) ∧ p1) ∧ True) ∨ False)) → p2) → (((p4 ∧ (((p5 ∧ p5) ∨ (p2 ∨ p2)) ∧ p3)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184444234111022634548369062969 : (((False ∧ ((p4 → False) → (p4 → (p5 ∨ p1)))) ∧ (p3 ∨ True)) ∨ ((p1 ∧ (((p1 ∧ p5) → ((p1 → p1) → True)) ∧ p1)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909193428793372233899537112950 : (((((((False ∧ p1) → (p4 ∨ p3)) ∨ p4) ∨ (((p1 ∧ (p1 → True)) ∧ p2) → (p4 ∨ False))) ∧ (((p2 → False) ∧ (p1 ∨ p5)) ∧ p2)) → False) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h22 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h23 := h19 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h25 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h26 := h19 h25
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h33 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h34 := h30 h33
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h36 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h37 := h30 h36
      -- False on the left can always be used.
      apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615894856971262045118080729828 : (((((p2 ∧ (False ∧ (((((p1 → p2) ∧ p4) → p1) ∧ (True ∨ True)) ∨ True))) ∨ (p2 → ((p2 → (p4 ∨ (False ∧ p2))) ∨ True))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_703683362346244757251179424257 : (((((((p2 → (p2 → True)) → (p1 ∨ False)) → p3) ∧ p5) → (((p2 ∧ (False ∧ p3)) ∨ (True ∧ (p5 ∧ p3))) ∧ ((True → p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767658797424348178701594017629 : (((p5 ∧ ((False ∧ (p4 ∨ (p1 → ((p1 ∨ False) ∧ (((p1 ∨ ((True ∧ ((p1 ∧ True) → p3)) ∧ (p1 ∨ False))) ∧ p5) ∨ True))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157586764037154595684654796886 : (((p4 ∧ ((((((p5 ∨ p4) ∧ (p2 ∨ p4)) ∨ p1) → p2) → (p3 ∨ p1)) ∨ p3)) → (p2 ∧ p4)) ∨ ((((p5 ∧ p5) ∨ True) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767263444144781058268356573668 : (((p5 ∧ ((((((p4 → p1) → True) ∧ ((p4 ∨ False) → ((p1 → p3) ∧ (True ∧ ((True ∨ True) → p1))))) ∨ p4) ∨ (p4 ∨ p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118280195015981479830503382617 : ((p1 ∨ (((False → True) ∧ p3) → (((p5 ∨ p4) ∨ ((p2 ∨ True) → ((((False ∧ p5) → (False → p3)) ∨ True) → p5))) ∨ p2))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198453311550583098841793048570 : ((p5 ∧ ((False ∧ (True → p3)) ∧ (p2 ∧ p3))) ∨ ((((((p2 ∨ p1) ∧ p4) → (True ∧ (True ∨ p2))) ∨ p5) ∧ (p2 ∧ True)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113361394066487736676804150090 : (((p5 ∧ (((p3 ∧ (p4 ∨ p5)) ∧ (((p3 ∨ (p4 ∧ ((p4 ∨ True) ∧ p4))) ∧ True) ∨ p2)) ∨ (p1 → p4))) ∧ (p2 ∨ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181307032361516656120614403785 : ((p5 ∧ (p4 ∨ (p5 ∧ (p2 ∧ ((True ∧ ((p3 ∨ p3) → False)) → p3))))) → ((((p1 ∨ (p5 → (True → p4))) → (p2 → p4)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767050513136613768148728383763 : (((p4 ∧ (p2 → (p2 ∧ ((((((p2 → p2) → (False ∨ (True ∧ False))) ∧ p1) ∧ ((p4 ∨ p1) ∨ (True → p5))) ∧ (p2 ∨ True)) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319775375479136518340271545664 : (p4 ∨ (((((p1 ∨ p1) ∨ True) ∨ p4) → False) → (p5 ∨ ((p3 ∧ (p5 ∨ ((p2 → (((p4 ∧ False) → p4) → False)) ∧ p3))) ∧ (p2 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p1) ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626981690710158512342889480205 : (((((((((((False ∨ (((True → p3) → p1) ∨ (p4 ∧ p1))) → p2) ∧ p4) → (p1 → (True → p4))) ∨ p1) → p1) ∧ p1) ∧ True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337522450221624914874595398454 : (p1 → ((((p2 ∧ p4) ∨ (((p4 ∨ p4) ∧ p4) ∧ (((False → (p5 ∨ False)) ∨ p2) ∨ (p4 → p2)))) ∨ p4) ∨ (p3 → (p3 ∨ (p4 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157013148598898485112539721405 : (((((p2 ∧ p3) ∨ p5) → (True ∧ (((False ∨ (p2 ∨ p3)) ∨ p5) → (False ∨ (False ∨ p5))))) ∨ False) ∨ ((p5 → ((True ∨ p1) → True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342754763149872682737956112470 : (p2 → (((((p2 ∧ False) → True) ∧ p4) → (p3 → False)) ∨ ((p1 ∧ (p5 ∨ (((p5 → False) ∧ (False → p2)) ∨ ((p1 → p2) ∧ True)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328118533840444236220697393471 : (True → (((p3 ∨ (True → ((p3 ∧ p5) ∧ (p4 ∧ (p3 ∨ ((p1 ∨ p3) ∨ False)))))) ∨ ((p1 → (p2 → p2)) ∨ p3)) ∨ (p2 ∨ (False ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28168121140421304828114832755 : ((True ∧ (((p1 ∧ (((p4 ∧ ((True ∧ (False ∨ (p2 ∧ p1))) ∨ ((p2 → p3) → False))) → p4) ∨ (False → (p1 → p3)))) → p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304715771869813551640293815849 : (p1 ∨ (((((False → p3) ∧ ((False ∨ p4) ∨ False)) ∧ (p3 → ((p3 → (p2 → (False ∨ p5))) ∧ p5))) ∧ ((p2 → False) ∧ p5)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793478610968386470189583109617 : (((True → (False ∨ (p3 ∧ (((p2 ∨ (((p1 ∧ (p4 ∨ (False ∨ False))) ∨ (p1 → p2)) → ((p1 → p3) → p4))) → p3) ∧ (p4 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68192190925006337576196897264 : ((p3 → ((((((p3 ∨ p1) → p1) ∨ p1) ∨ (p2 → p5)) → ((p5 ∨ (p1 ∧ p4)) ∨ (True ∧ ((False ∧ p3) → (False → True))))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37419535178547548878706332807 : (((((p4 ∨ ((False → ((((((p2 ∧ p2) ∨ (True ∧ p5)) ∧ p1) ∨ p4) ∨ (p3 → p5)) ∨ False)) ∨ p4)) → (p3 ∨ False)) ∨ False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601793812831869945756781683973 : ((((p4 ∧ (((((((((p5 ∨ p1) → True) → p2) ∨ False) → (p3 ∧ p5)) → p2) → p4) ∧ ((p1 → True) ∨ p5)) ∨ (False → p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38757630995823835542110703116 : (((((p1 → p3) → (False → True)) ∧ (((((p3 ∧ p4) ∧ True) ∨ (((p3 ∨ p1) → p4) ∨ ((p1 → False) → p4))) → p2) → p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208805699775636353398335460430 : ((p3 ∧ ((p5 ∧ (p2 ∧ p2)) ∧ True)) → (((False ∨ p4) ∨ ((p1 ∨ (((True → p4) → p1) ∨ (p3 ∧ (p2 ∨ p2)))) ∧ True)) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178130545042918756255738689984 : ((((p5 → (p1 ∨ (p1 → (True ∧ True)))) → ((p5 ∨ p4) → p1)) → p4) ∨ (False ∨ ((((p5 ∧ p4) ∨ True) ∨ (p2 ∧ (p2 ∨ p4))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_119199036151734335383456513305 : ((p2 → ((((p5 ∧ (False ∨ ((p2 ∧ (p3 ∧ p1)) ∧ p5))) ∨ True) ∨ ((p5 ∧ p5) → p1)) ∧ (p5 → ((p2 ∧ p5) ∧ True)))) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137327693336909212401062877505 : ((p2 ∧ (False ∧ (((((p5 → ((False → p3) → (p3 ∨ p2))) → ((p5 ∨ p5) ∧ p1)) → p3) ∧ (p3 ∨ p5)) ∨ p1))) ∨ ((True ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134372142148895898723327003579 : (((p2 ∨ (p4 ∧ (((True → (((p5 → (p2 ∨ p2)) ∧ p3) → p2)) ∨ True) ∨ (p5 ∧ ((False ∨ p4) ∧ False))))) ∨ p1) ∨ (p2 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173210650727745267171131792118 : ((p5 ∨ ((((True ∧ p4) ∨ p3) → p3) → (False ∧ (((p4 ∧ p3) → p4) ∨ True)))) ∨ (((((p4 ∧ p1) ∨ p5) → p2) → True) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657090319860750727764274777714 : (((((p3 → (False ∨ False)) ∧ ((p4 → ((p3 ∨ ((p5 → (p3 ∧ False)) → p1)) → (p1 → False))) ∧ (p1 → (p5 ∨ p2)))) ∨ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53548082715134885219616853579 : (((((False ∨ p3) → (False ∨ (False ∧ (p1 ∨ True)))) ∧ p1) ∧ (p2 ∧ (((p2 → False) ∧ ((False ∨ (p5 ∧ False)) → (False → p5))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319863745386150843200575198464 : (p4 ∨ ((((False ∨ p1) ∨ True) → p5) ∨ ((((p2 ∨ p4) → p4) ∧ ((p4 ∨ (p2 ∨ (((False ∨ p2) ∧ (p3 → True)) → p5))) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318648036906713377544640804684 : (p4 ∨ ((p5 ∨ ((p1 ∧ (p4 → True)) ∧ (p5 → ((((True → ((False → False) ∧ p4)) ∨ (p1 ∨ p1)) ∧ (p3 ∨ p2)) ∧ True)))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314931363278941501911627012438 : (p3 ∨ ((True ∧ (p5 ∧ ((p4 ∧ (p4 → p2)) → (False ∧ p5)))) ∨ (p1 → (((p1 ∨ (p3 ∧ ((p3 ∨ (p5 ∧ p5)) ∧ p1))) ∧ p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213921202428727095222125086168 : (((True → (p1 ∨ p1)) ∨ p3) ∨ ((p3 ∨ p5) ∨ ((False ∧ ((((p5 → False) ∧ (p2 ∨ True)) ∨ False) → (p5 ∨ p3))) → ((p2 → False) → True)))) := by
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
theorem thm_5_vars_615046103088306018362150901816 : (((((p4 ∧ (p1 → (p4 ∨ ((p5 ∨ True) ∨ (p5 → ((True → p3) → ((p2 ∧ True) ∨ p2))))))) → ((p4 → p2) ∧ (p4 ∧ p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892853340247110661185932509834 : ((((((((p1 → ((p5 ∨ False) ∧ p1)) ∨ p5) → (p5 → ((False ∧ p3) ∧ p5))) → p2) ∧ ((False → p2) → p5)) ∧ (p3 → (False ∧ p4))) → p5) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_557650660897023583683084518759 : (((p3 ∨ ((p5 ∨ p5) → ((p3 ∨ p3) ∨ (False → (((False ∧ p4) → (p4 ∨ (False ∧ True))) ∧ (p1 ∧ ((p1 ∨ (p4 ∨ p5)) ∨ False))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159928084028311936077369098847 : (((((p1 ∧ True) ∧ (False → (((False ∧ (p4 ∨ p4)) ∨ (p1 ∨ p1)) ∨ (p5 → p1)))) → p1) → p5) → (p2 → ((True → p4) ∨ (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ True) ∧ (False → (((False ∧ (p4 ∨ p4)) ∨ (p1 ∨ p1)) ∨ (p5 → p1)))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746742006139790475737595508353 : ((((p3 ∨ p3) → (((p4 ∨ ((((False ∧ (p4 ∧ p1)) ∧ (False ∨ p1)) ∨ p3) ∨ p5)) ∧ (p5 ∧ p4)) ∨ ((False ∨ (p3 ∨ p5)) → True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_651178258170056905435475201202 : (((((((p4 ∨ True) ∨ True) → p2) → (p2 ∧ (p4 → ((p5 ∨ p1) → (((p4 → (p1 → False)) → p1) ∧ (False ∨ p1)))))) ∧ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136691881286592493696907414776 : (((True ∧ p2) ∧ (p5 ∨ ((((p4 → ((p2 ∨ (((p4 ∨ p5) ∧ False) → p5)) ∨ p5)) ∨ False) ∨ (True ∧ p1)) → p2))) ∨ (p4 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343276951294051558089110436751 : (p2 → ((p2 ∧ p2) ∧ (p3 → (((p3 → p1) → ((p2 → ((p3 ∨ (p4 ∧ p5)) ∨ p4)) → (True ∧ (p5 ∧ ((p5 ∧ p3) ∨ p4))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114722438243943392034861130024 : (((((True ∧ True) → ((p3 → (True → p2)) ∨ ((p4 ∧ p3) ∨ True))) → (p1 → True)) → (p5 ∨ ((p3 ∧ (False → p1)) ∨ p5))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114494820390075430350617764045 : ((((p5 ∨ ((p5 ∨ ((p5 ∨ p1) ∧ True)) → p3)) ∨ (True ∧ (((p2 ∧ p4) ∧ True) ∧ False))) → ((p1 ∧ False) ∨ (False ∨ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208745299800834715802228852250 : ((p1 ∧ (p2 ∨ ((p4 → p3) ∧ p3))) → (((p5 → ((True ∨ p4) → (p5 → p2))) ∨ (True ∧ (((p2 ∧ p3) ∨ p5) ∨ (p2 ∨ p4)))) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53810412901569168243355720162 : ((((p5 → (((p3 → True) ∧ p3) → (p1 ∨ p5))) → p1) ∨ (((((((p1 ∧ p4) → (True → False)) → p2) → p5) ∨ p4) ∧ p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229701613046783832331766220437 : ((p4 → (False ∧ p1)) ∨ (((((p3 ∧ p2) → p2) ∧ p1) → ((((p4 ∨ p1) ∨ p1) → p5) ∨ ((True ∨ p4) → p5))) ∨ (p1 → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625120067347663103306939003162 : ((((True → ((((((p1 ∧ (p3 ∧ p2)) ∧ p2) ∨ True) ∧ ((((p2 → True) → False) → p2) ∨ p1)) ∧ False) ∨ (p1 ∧ (p3 → p3)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761856179383318484701740319018 : (((p3 ∧ ((((((((p2 ∧ ((p4 → False) → (False ∨ p1))) → (True ∨ p4)) ∨ p2) → (p2 ∨ True)) → p4) → p3) ∧ (p3 → True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338289202350786226477516972799 : (p1 → ((p3 ∨ ((p5 → (False ∨ True)) → True)) → ((((((p4 ∨ (False → (p5 → (p1 → p3)))) ∨ p4) ∨ p2) → (p2 ∨ True)) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164552192924358211130009516361 : ((((p4 ∨ ((p2 → (p5 ∧ True)) → p3)) ∧ (False ∨ (True → ((p2 ∨ p4) ∧ p1)))) ∧ p4) ∨ (((p2 ∧ False) → False) ∨ ((p5 ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_137540881269638129173303711522 : ((p5 ∧ (p2 → (p2 ∧ ((p4 → (False ∧ ((False → (((p5 ∨ p5) → (False ∧ False)) → (p3 ∨ False))) ∧ True))) → p4)))) ∨ ((p3 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738160637486149445535733428880 : ((((False ∧ p2) ∨ (((p1 ∨ (False ∨ ((p5 ∨ True) → (p3 → (p3 ∨ (False ∧ (False → False))))))) ∨ p2) ∧ ((p1 → p2) → (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316985927753418426319206425074 : (p3 ∨ (p3 → ((p1 → ((((((p2 ∨ True) ∧ p1) ∨ (False ∧ p3)) ∧ (p5 ∨ False)) ∨ False) ∧ ((p5 → (p1 ∨ True)) ∨ p2))) ∨ (False ∨ p3)))) := by
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
theorem thm_5_vars_355554260587997785674573238452 : (p5 → ((((False → ((p2 → p4) → p3)) ∧ ((True ∨ (False → p4)) ∨ (False ∧ (True ∧ (((p3 ∧ False) → p5) ∨ p5))))) → False) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53762819187622469335991553239 : ((((p3 ∨ (p4 ∨ ((p4 ∧ False) ∧ (True ∨ True)))) ∧ p3) ∨ (False → (((((p2 ∧ p5) ∧ ((p1 ∨ p4) ∨ p1)) ∧ p4) ∨ p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337668475785586837413128012484 : (p1 → (((p3 ∨ (p1 ∧ p3)) ∨ ((p4 → ((((p3 ∨ p5) ∨ True) → p2) ∧ True)) → (p4 ∨ p3))) ∨ (((True ∨ (p4 ∨ p2)) ∨ False) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156902354645677389787967609723 : ((((p2 → (((p1 → (p3 ∨ (True ∨ p1))) ∧ p3) → (p4 → (p4 ∧ (p1 ∨ False))))) ∨ p5) ∨ True) ∨ (True ∨ (False ∨ (p3 ∨ (p3 ∧ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645444330456516566719846920 : ((((((((p4 → p3) ∧ p2) → p1) ∨ (((True → p4) ∧ p4) ∧ p5)) ∧ (p4 ∧ (True ∨ p1))) → p5) ∨ ((p2 → p2) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309057466357779868147265784337 : (p2 ∨ (((p2 → p2) → ((((p5 → (True ∧ p4)) ∨ ((p1 → ((True → p3) → (p5 ∨ ((p1 ∧ p1) ∧ p2)))) ∧ True)) → True) ∧ False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178252207144916569837135454857 : ((((p5 → (((p4 ∧ True) → (p3 ∧ p3)) → p1)) ∨ p2) ∧ (p3 → p4)) ∨ (True ∧ (p5 ∨ ((p2 → (False ∨ ((p1 → p1) ∨ p3))) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244952192981156812740000769890 : ((p1 ∧ p3) ∨ ((p1 → p3) ∨ (((((((p3 → (p1 ∧ ((True ∧ False) → p1))) → p4) → p1) ∨ False) → (p5 ∧ p5)) → p4) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_354822673719175693253791878442 : (p5 → (((p1 ∧ (p3 ∨ p2)) ∨ (p4 ∨ (((False → p2) → p3) ∧ (((p4 ∨ False) ∨ (p4 ∨ (p2 ∨ p1))) ∧ ((p4 ∨ p5) → p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631415547020639583334242743255 : (((((((p1 ∧ ((p3 → p4) ∨ (((False ∧ (False ∨ False)) ∨ p5) ∧ p5))) ∧ (p4 → ((False ∨ False) ∨ False))) ∨ (p1 ∨ True)) → False) → p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ ((p3 → p4) ∨ (((False ∧ (False ∨ False)) ∨ p5) ∧ p5))) ∧ (p4 → ((False ∨ False) ∨ False))) ∨ (p1 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133519979978291193983190757122 : ((((((((p3 ∧ p2) → (((p5 ∨ p1) ∨ p3) ∨ (p2 ∨ True))) ∨ p3) → (p3 ∨ (p1 → p3))) → p4) ∧ True) ∧ p2) ∨ ((p1 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136776305369534279883928920381 : (((True → True) ∧ (p2 ∧ ((((p1 ∧ (p3 ∧ (p4 ∧ True))) ∧ (p2 ∧ True)) → p2) → (True ∧ (p4 ∨ (p2 ∧ p1)))))) ∨ (False → (False ∧ p3))) := by
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
theorem thm_5_vars_244294233527378371346949368345 : ((False ∧ True) ∨ (p2 ∨ ((p1 ∧ ((((p3 ∧ p2) ∨ ((p5 ∨ True) ∨ p2)) ∨ (((False ∧ (True ∧ p4)) ∧ p5) ∨ (p3 → p1))) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709714308334147472679925626563 : ((((True → (((p1 ∨ p3) ∨ p3) ∧ (p5 ∧ p1))) → (((p1 → (p5 ∨ (((False ∨ True) ∨ False) ∨ ((p3 ∧ p3) ∧ p1)))) ∨ p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52252365216387021724267373963 : (((p1 ∨ (((False ∨ p3) ∧ ((p4 → p4) → (p5 ∨ (p5 ∧ p5)))) → (p5 → p3))) → ((p5 → (p3 ∨ ((p2 ∧ True) ∧ False))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337546409750562402915106113228 : (p1 → (((False ∨ p5) ∨ ((((p3 → p4) ∨ (((p4 ∨ False) ∨ (False ∨ False)) ∨ (p5 ∧ p3))) ∧ p1) → p3)) ∨ (False → ((p3 ∧ True) ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682346621316507471949974396922 : (((((p5 ∧ (p1 ∧ (p3 → (((p5 → (p1 → False)) → (True → False)) ∨ p2)))) ∨ (p2 → p1)) ∧ ((p5 → p4) ∧ (p2 ∧ (False ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159019231853225099628466473506 : ((p4 ∨ (((((False → p3) → p4) → (p4 ∧ (True ∧ p1))) ∨ False) → (p2 ∨ ((False ∨ p1) ∧ True)))) ∨ (((p4 ∨ False) ∧ False) → (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299132415083090890461847340304 : (False ∨ ((((p4 ∨ ((((p4 ∧ False) ∨ (((True → True) ∨ False) ∨ p2)) ∨ p3) → ((p1 ∨ (True → p2)) ∨ p3))) ∧ (False → p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40534683867266673312181649899 : ((((p2 ∨ ((p2 ∧ True) ∧ ((p5 ∧ ((True ∧ False) → p1)) → (((True → (True ∨ p1)) → (p4 ∧ (p1 ∨ p5))) → False)))) ∨ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173130324275336975659424655813 : ((p2 ∨ (p3 ∨ ((((False ∨ (True → True)) ∨ (p1 → (True ∨ p1))) ∧ p3) → p1))) ∨ ((True ∧ (p1 ∧ True)) ∨ ((False ∨ p5) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157436515145684238608181925012 : (((p5 ∧ ((p1 → ((((False → p5) → p3) → ((p1 → p3) → p3)) ∧ p1)) → p2)) ∧ (p1 ∧ p5)) ∨ (p5 → (True ∨ (p3 ∨ (True ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63253343655323123634984355648 : ((p5 ∧ (((p5 ∧ (p1 → (p3 ∨ True))) ∧ (True ∧ p4)) ∧ ((False ∨ (((p3 ∧ ((False ∨ p3) ∨ (False ∧ True))) ∨ p2) → p3)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149490656933743310003348167683 : ((p1 ∧ (((((False → p5) ∧ (p1 ∧ (((p4 ∧ False) ∨ p4) ∨ p4))) ∧ (True → p1)) ∧ (p1 ∧ True)) ∨ p5)) ∨ ((True ∨ (True ∨ p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40530748925932085372134624265 : ((((p1 ∨ (((p5 ∧ (p5 ∧ p4)) ∨ p5) ∨ (((p4 → True) ∨ ((p4 → (p4 ∧ (p1 → (p3 → True)))) → True)) → p3))) ∨ p5) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137185200649191233377298713050 : ((False ∧ ((p2 → (p4 ∧ (p1 ∨ p2))) ∨ (((p3 → p4) → ((True → False) ∧ (p1 → p5))) ∧ (False ∨ (p3 ∧ p2))))) ∨ ((p5 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43843755151580886978280581431 : ((((((p5 → p5) → (((True → ((False → p3) ∧ p2)) ∧ (p4 ∨ False)) → (((False → False) ∨ p5) → p2))) → False) ∧ (False ∨ p3)) → p2) ∨ p3) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p5 → p5) → (((True → ((False → p3) ∧ p2)) ∧ (p4 ∨ False)) → (((False → False) ∨ p5) → p2))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h15 := h11 h14
          -- We need to get the right conjuct of h15 based on <expert-advice>.
          let h16 := h15.right
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h8.left
        let h20 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h23 := h19 h22
          -- We need to get the right conjuct of h23 based on <expert-advice>.
          let h24 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h6
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50291088190375834365494266423 : (((((False ∨ (((((p4 → True) → p3) → p2) → True) → p2)) ∨ (p5 ∧ False)) ∧ ((p5 ∧ False) ∧ True)) ∨ (True ∨ (p5 → (False ∧ p1)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49527075023970071354558077662 : (((((True ∧ (((False ∨ p1) → (p5 ∧ (p5 ∨ (p3 ∨ p5)))) ∨ p5)) ∨ (True ∧ (p5 → True))) ∨ (p3 → p5)) → ((True → p1) ∨ True)) ∨ False) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
theorem thm_5_vars_52915701268009267385188699832 : (((p4 → (p3 ∧ ((p5 ∧ True) ∧ (((p3 ∧ (p5 → p2)) ∨ p2) ∧ p3)))) → (p2 ∨ (p5 → (p3 → (((p5 ∨ p3) ∨ p3) → p5))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191812464394985074915357860212 : ((p2 ∨ ((p5 → True) → (p4 ∨ ((p4 ∨ p2) ∧ p4)))) ∨ (((p1 ∨ (((((p3 → p3) ∨ (p1 → p2)) → p1) → p4) ∧ False)) ∨ p1) → p1)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



