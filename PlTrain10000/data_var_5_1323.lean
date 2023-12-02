variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112336518908058766675574529144 : (((p4 → (p2 ∨ (p2 ∨ (p3 → ((p1 ∧ (p2 ∧ (p2 ∧ (p2 ∨ (((False ∨ (True ∨ p3)) ∧ p2) ∧ p3))))) ∨ p4))))) ∨ p3) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115734455103446326877005444263 : ((((p2 → (p4 → p4)) ∨ (False ∧ p1)) → ((((((p1 ∨ True) ∨ ((p2 → p2) ∨ p3)) → p1) → p2) ∧ p5) ∨ (True ∧ True))) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780269785762294136014593361229 : (((p2 ∨ ((p5 → (p2 → ((((p1 → (p2 ∨ False)) ∧ p4) → False) → (((p5 ∧ (p1 → True)) ∨ True) ∨ p2)))) → ((False → False) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167640319016950348245825897196 : ((((False ∧ (True → (p1 ∧ ((p5 ∧ p1) ∧ p1)))) → ((p5 ∧ p3) ∨ True)) → (p3 ∧ p3)) → (p1 → (p4 ∨ (((p1 → p5) ∧ p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322414034049370687775528958702 : (p5 ∨ (((False ∧ (p2 ∨ (True ∧ (p2 ∨ ((p3 ∧ False) ∨ False))))) ∨ (p2 ∨ (((((p3 ∧ False) → (p5 ∧ False)) ∧ p3) ∧ p1) → p1))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300057445802347004972414482590 : (False ∨ (((True ∧ (False ∨ (p5 ∧ (p5 ∨ (((False ∨ p5) → (((p2 → p3) → (False ∧ False)) ∨ (p5 ∨ p1))) ∧ p4))))) ∧ p5) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114937958314022133722866858696 : ((((p4 ∨ (p5 ∧ (True ∨ False))) ∧ (p3 ∧ (p1 ∨ (p1 ∨ (p4 → p2))))) → (p3 → ((p5 ∨ (True ∨ p1)) ∧ (p4 ∨ p5)))) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h4.left
      let h17 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h24.left
      let h37 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h33
    case inr h42 =>
      -- False on the left can always be used.
      apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301741415298631175968092300632 : (False ∨ ((p1 → p1) ∧ ((p5 ∨ (p5 ∨ ((p3 → ((p3 ∧ False) ∨ (p5 → True))) → (p1 ∨ p4)))) ∨ (p3 → (p4 ∨ (p1 ∨ (p3 ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142969800865101370886342446688 : ((True → (((p1 → (True ∨ (p3 → p4))) ∨ ((((p1 ∨ (p2 ∨ ((p4 ∧ p4) ∨ p4))) ∨ True) ∧ p1) ∨ p4)) ∧ p4)) → ((p3 → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654194965734796778210440360489 : ((((((False ∨ (((p1 ∧ ((True ∨ True) ∧ ((p2 ∨ (p5 ∧ (False ∨ p5))) ∧ p3))) ∧ p5) ∧ (p4 ∨ p1))) ∨ False) ∨ True) ∨ (p1 ∨ p5)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_308457355653115212287399249892 : (p2 ∨ (((((((p1 ∨ ((((p3 ∨ p5) → (p1 ∨ (p3 → p2))) ∧ (p1 ∨ p3)) ∨ p3)) ∨ p2) ∧ p2) ∧ p2) ∨ p4) ∨ (p4 → True)) ∨ p3)) := by
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
theorem thm_5_vars_660957616135648638771238943438 : (((((p4 → (((p2 ∨ False) ∧ (p1 ∨ (p5 ∨ p3))) ∨ (p5 → ((((p1 → (p1 ∨ p5)) ∧ p3) ∧ p2) → p5)))) → False) → (p4 → p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (((p2 ∨ False) ∧ (p1 ∨ (p5 ∨ p3))) ∨ (p5 → ((((p1 → (p1 ∨ p5)) ∧ p3) ∧ p2) → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h3
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177942773289958506614570768029 : (((((p1 → p5) ∧ p4) ∨ ((((False ∧ p5) → p4) ∨ p5) ∧ False)) ∨ p5) ∨ ((((p4 ∨ True) → (p3 ∨ p1)) ∨ True) ∨ (p3 ∧ (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88110900648472742900136398413 : ((((p1 ∨ (p1 → p5)) → p4) ∧ (p4 ∧ (((p5 → (p4 → p3)) → ((p2 ∧ ((p5 ∧ (p3 ∧ True)) → (p1 ∨ False))) ∨ p2)) ∧ p5))) → p4) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482226748543192251661166831076 : ((((((False → p2) → ((False → False) ∧ p1)) → p4) → ((p1 ∨ p4) ∨ (True ∨ (((p4 ∨ (False ∨ p1)) ∧ (p2 ∧ p2)) ∨ (p5 ∧ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706183404735568039426776568015 : ((((True ∧ ((p1 ∧ p5) ∧ (p4 ∧ (p2 ∨ p5)))) ∧ (((p2 ∨ False) → (p5 ∨ (p2 ∨ (True ∧ ((p2 ∨ True) ∨ True))))) ∧ (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216219124665219074006021484854 : ((p1 → ((p4 → p4) ∧ p5)) ∨ ((p3 ∧ ((((p2 → p1) → (p4 ∧ True)) ∨ (((p5 → p1) → False) ∧ (p3 → (p2 → p2)))) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141101025443835131621167895342 : ((((p5 → ((p3 ∧ p5) ∧ (p5 ∧ True))) → p5) → ((((p1 ∧ (p3 ∧ p1)) ∨ (p4 ∨ (p4 ∨ p2))) ∧ p5) → p3)) → ((p1 ∧ p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115779272058839694180220002812 : (((((p2 ∨ True) ∨ p5) ∧ p5) ∧ (((p4 ∨ (p2 ∧ (False → ((p2 → p3) ∧ p4)))) → ((p3 ∧ (False ∨ p3)) ∨ p5)) → p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346803930850350505450403327677 : (p3 → ((True → (p4 ∧ ((((p5 ∨ p2) ∧ ((p2 ∧ ((p2 ∧ False) → p5)) ∧ (p3 ∨ False))) ∧ False) ∨ p4))) ∨ (False → ((False → False) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614275593650627106506564038923 : (((((((False → p2) ∧ ((True ∧ (p3 ∨ (p3 → p1))) ∧ p5)) ∨ ((p1 ∨ p4) ∨ ((p1 ∧ True) ∧ p3))) → ((p3 ∧ p4) ∨ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341733207660641473733308721651 : (p2 → (((p3 ∧ p3) ∧ ((((p4 ∨ p4) ∨ p5) ∧ p3) ∧ (((((p5 → True) → p1) ∧ p2) ∨ (True ∧ (p3 → p2))) → p1))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348739225504764754177282947604 : (p3 → (False ∨ (((p2 ∧ (((p3 → (p2 ∧ (p1 ∧ p1))) → (p2 ∧ True)) → p1)) → (p4 ∧ (p3 → (p5 ∨ (p4 ∨ p5))))) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342476709858677104468468962364 : (p2 → (((p4 ∨ (p3 ∨ ((p1 ∨ ((p4 → False) ∨ (p2 → p4))) → p5))) ∨ False) ∨ (False ∨ ((False → p1) ∨ (((p1 ∧ p2) → p5) ∨ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739144044391521888731112397148 : ((((p4 ∧ True) ∨ (((((False ∨ p4) ∨ (False ∧ True)) → (True ∨ (((p5 ∧ p4) ∧ (False ∨ p4)) → p1))) ∧ p4) → ((p2 ∧ p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116784372331360118090645286891 : (((p1 ∨ p2) ∨ ((((True → False) ∧ ((p2 ∨ (False → (p4 → ((p3 ∨ (p4 ∨ p1)) ∧ (p3 ∨ p1))))) ∨ p5)) → False) ∧ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170414723827768498706339777162 : ((((p5 → True) → False) ∨ ((True ∧ ((False → p5) ∨ p5)) ∧ ((p1 ∧ p4) ∨ True))) ∧ ((True ∨ (((False ∧ p3) → True) ∨ (p1 ∨ False))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601465263122218493411747535131 : ((((p3 ∧ ((((p1 ∧ (p3 → p3)) → ((p3 ∧ (p2 ∧ p5)) ∨ (((p2 ∨ (p5 → p3)) → p2) ∨ True))) ∨ (p5 ∨ p3)) ∨ p3)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54976555627075543634445632052 : ((((True ∧ p2) ∧ ((p2 ∨ True) ∨ p4)) ∧ (((p3 ∧ False) ∨ (False ∧ ((p3 ∨ (p2 → p4)) → False))) ∨ (p1 → ((p3 ∨ p4) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117244237693323424380565556662 : ((True ∧ (p2 ∨ (((((True ∧ p1) → p2) ∧ (((((p4 → (p2 ∨ p1)) ∨ True) ∧ p1) ∨ (True ∧ False)) ∧ p1)) ∧ False) ∨ p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329021466627874719334625667313 : (True → (((((False ∨ p3) ∨ False) ∨ True) → p5) → ((True ∧ ((p2 → ((p2 ∨ ((False ∧ p5) ∧ (p3 ∨ p4))) → False)) ∧ p1)) ∨ (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ p3) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((False ∨ p3) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164577095629077461855658375533 : (((((p1 ∨ p2) ∧ p3) → ((p3 ∧ (p4 ∨ (p5 ∧ p4))) → ((p1 ∨ p1) → p5))) ∧ False) ∨ (((p3 ∨ p3) → True) ∧ ((False ∧ p4) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244153362286706562877425019411 : ((True ∧ p4) ∨ ((((((False → p5) → False) → p3) ∧ False) ∨ p5) → ((((False ∨ p4) ∧ p2) ∨ ((True ∧ False) → False)) ∧ ((p4 → p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300108187090770954361440268746 : (False ∨ ((((p2 → ((False → True) ∧ (p1 ∨ (p4 ∧ p1)))) ∨ p1) ∨ ((False → (((p3 ∨ p4) → (True ∨ p5)) ∨ True)) ∨ False)) ∨ (p5 ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356720376534335001314820580977 : (p5 → (((p5 ∧ ((p2 ∨ p2) ∧ p1)) ∨ p1) ∨ (((p3 ∧ p3) ∨ p4) → (((True ∧ p2) → False) → (p3 → (p2 ∨ ((p5 → True) ∨ p5))))))) := by
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
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340678818821961933087363139145 : (p2 → ((p4 → ((True → (((p5 ∨ False) → ((((p2 → True) ∧ True) → (((p1 ∧ (p5 ∧ p4)) ∨ p3) ∧ p2)) ∨ True)) ∧ False)) → p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49517162981782834977032355132 : (((((p4 → (p2 → p4)) ∨ ((False → p1) ∨ (((((p4 ∧ True) ∧ p1) → p2) ∨ p5) ∨ p4))) ∧ (p1 ∧ True)) → ((p5 ∨ False) ∨ True)) ∨ p2) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h3.left
          let h15 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h3.left
          let h18 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h3.left
        let h21 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245671425738541193445254346405 : ((p3 ∧ p1) ∨ ((p2 ∧ ((p5 ∧ True) ∧ (p2 ∧ (False ∧ True)))) ∨ (((False ∧ p5) ∧ True) ∨ ((False ∧ (p5 ∨ (p4 → False))) ∨ (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164444817004477558869708001852 : (((((True → (p5 ∨ ((p3 ∧ False) ∨ ((p1 ∨ (p3 ∨ p1)) → p5)))) ∨ True) ∧ p4) ∧ p1) ∨ ((p1 ∨ p1) ∨ ((p1 → (p2 → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59886102733455959780712503828 : (((p4 ∧ p5) → ((True ∧ ((((False ∨ (p3 ∧ ((p4 ∧ p5) ∧ (p3 → True)))) ∧ True) ∨ (p5 ∧ False)) ∨ p3)) ∨ (False ∨ (True → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191932911808692638572243279449 : ((True → (((False ∧ (False ∧ p2)) ∧ p5) ∨ (p3 → False))) ∨ (((False ∧ ((p5 ∧ p4) → (((p5 ∧ p4) ∧ (True → p3)) → p5))) ∧ p5) → p4)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713215391612921904220809283562 : ((((p2 ∨ ((p1 ∨ p1) ∧ (True ∨ p5))) ∨ ((p4 ∨ p2) → ((((False ∧ True) ∨ (p2 ∨ (p4 ∧ p2))) ∨ True) → (p4 ∨ (True ∨ p2))))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215269276034218257926795051935 : ((False ∧ (p4 ∨ (p5 ∧ p5))) ∨ (p3 → (p5 ∨ ((p5 ∧ ((True → (p2 ∨ p3)) ∧ (((p2 → p5) ∨ (p4 → p2)) → (False ∨ p1)))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → p5) ∨ (p4 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43938759504211607071386928221 : ((((((p5 → (False → True)) ∨ (((p2 → False) → p3) ∧ p1)) ∨ ((p3 ∧ p1) → (True → (True → (p2 → p3))))) ∨ (p4 ∧ p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65326321224151061197810008448 : ((p3 ∨ (((True ∧ (p4 → (False ∨ (False ∧ ((p3 → ((p3 ∧ (p2 ∧ p4)) → False)) ∨ False))))) ∧ True) ∧ ((p1 → (p4 → True)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188827450795715369057853216245 : (((((p4 → p3) ∧ p5) ∧ p3) ∨ ((p3 ∧ True) → True)) ∧ (((True ∧ (p2 ∧ (True ∧ False))) ∨ (p2 ∨ (p5 ∧ ((p5 → p1) ∨ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193171885186834333996558878675 : ((((p4 → (p5 ∧ p2)) ∧ p4) → ((p4 → False) ∧ p5)) → ((p5 ∧ p5) ∨ ((p2 → p5) → (p2 ∨ ((p1 → p3) → (p5 ∨ (p2 → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741102134652655805689588501419 : ((((p4 ∨ False) ∨ (((((((p5 → p4) ∧ (p3 → True)) ∨ p3) ∨ True) ∧ (p1 ∨ True)) ∨ (((True → p5) ∧ (True → p5)) ∧ p3)) ∨ p2)) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185273705526526919309750324391 : ((p1 ∧ (p1 → (p1 → ((True → p1) → (False ∨ (p5 ∧ p3)))))) ∨ ((((False ∨ p3) → ((p2 → (p4 ∨ p4)) → True)) ∧ True) ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136666941052772623127056409243 : (((False ∨ (p4 → p3)) → ((p3 ∧ ((((p3 ∨ True) ∧ p5) → True) ∧ ((p1 ∨ (p1 ∧ p4)) → p2))) → (p3 ∨ True))) ∨ ((p2 ∧ p5) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41648687659154057795092672781 : ((((((False ∨ p3) ∨ p4) ∧ (p1 ∨ p2)) ∧ (False → (p2 → ((p1 ∧ ((p2 → (p4 → p3)) ∨ p4)) ∨ ((p1 → p2) ∧ p5))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321208219829814391023910724639 : (p4 ∨ (p3 ∨ (True ∧ (((((p4 ∧ p1) ∨ False) ∨ p1) ∨ (True ∨ p2)) ∧ (True ∨ (((p1 ∨ (p4 ∧ (p4 → p3))) ∨ p4) ∧ (p5 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165393923202623990486423022060 : (((p4 ∧ (p5 ∧ (((True ∨ False) → False) ∧ (p1 ∨ (True ∧ p5))))) ∨ (True ∨ (True ∧ True))) ∨ (((False → (p2 ∨ (p3 ∧ False))) → p5) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133502235255066328064731457228 : ((p5 → (p4 ∨ ((((False ∨ (((((p4 ∧ p5) → p1) ∨ False) ∨ p2) ∧ p2)) ∨ (p1 ∨ p4)) ∧ p1) ∨ (p5 ∧ p5)))) ∧ (False → (p5 ∧ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598259351617091945234912283329 : (((((False ∧ (p2 ∧ True)) ∨ ((((((p1 → (p1 ∨ p3)) ∧ (True ∨ True)) ∧ p1) → (p5 → p5)) → (p4 → False)) ∧ (False → p4))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57984557619781431157620947188 : (((p4 → (p4 ∨ False)) → ((((((p1 ∨ p5) → p5) → (p1 → (p5 ∨ False))) ∧ p5) ∧ p2) ∨ (((p4 ∧ (False ∨ p3)) → False) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164747272357417133505684887324 : ((((p5 ∨ (p1 → (p4 ∨ (((False ∨ p1) ∨ p4) → (p5 ∧ p4))))) ∨ (True ∨ p3)) ∨ p3) ∨ (p2 ∨ (p1 → (p2 → (p2 ∨ (True ∨ True)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136448400019402006042450137495 : (((p4 ∧ (False ∨ (p1 → p3))) → ((p3 → False) → ((((p4 → (p2 ∧ p4)) ∧ (p2 ∨ p5)) ∨ (p3 → p2)) ∧ False))) ∨ (p4 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246713132775267869990862341757 : ((p5 ∧ p4) ∨ ((p5 ∨ p3) ∨ ((p2 ∨ False) ∨ (((p3 ∧ False) ∨ ((p5 ∨ ((p1 ∧ p1) → (p2 → p5))) ∨ (True → True))) ∨ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173892210019956534633154394152 : ((((p5 ∧ ((p5 → False) → ((((True → p5) ∨ True) ∨ p3) ∧ p1))) ∨ True) → False) → ((((p4 ∧ (p2 ∨ (p5 ∨ p1))) ∧ True) ∧ p1) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ ((p5 → False) → ((((True → p5) ∨ True) ∨ p3) ∧ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ ((p5 → False) → ((((True → p5) ∨ True) ∨ p3) ∧ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ ((p5 → False) → ((((True → p5) ∨ True) ∨ p3) ∧ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∧ ((p5 → False) → ((((True → p5) ∨ True) ∨ p3) ∧ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172757787563249405513844503183 : (((p4 ∧ p2) → (((p3 ∨ True) → (p5 → (((p3 ∧ p1) ∧ p3) → False))) ∧ False)) ∨ (((True ∧ p4) ∧ p4) ∨ (p5 → (p5 ∨ (p5 ∨ p2))))) := by
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
theorem thm_5_vars_616553523282102214725560163982 : ((((((((p4 ∧ p5) ∧ p3) ∨ (p4 ∧ (p4 ∨ True))) ∨ False) ∧ ((((((p3 ∨ p4) ∧ p2) → (True → p1)) ∨ True) ∧ True) ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_168296712517949264273882914216 : (((p1 ∨ True) ∧ (((((p4 → (p5 → (p3 ∨ p2))) ∧ False) → p3) → p5) → (p2 ∨ p3))) → (((((p5 ∧ p1) → p2) → p3) ∨ True) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47426885006906474076930312734 : (((p1 ∧ (p5 ∨ (((p2 → p1) ∨ ((p3 ∨ p2) → (p3 ∨ p3))) ∧ (((p3 ∧ p1) ∨ p1) ∨ ((p3 ∧ p4) ∨ True))))) ∨ (True ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41795886189967840868330036525 : (((((p3 → p4) → (p5 ∧ p3)) → (p5 ∧ ((((((True ∧ p4) → ((p3 → p1) → p1)) → p5) → p4) → (p4 ∧ True)) ∨ False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33437346046926285498381961978 : ((p4 ∨ (((False ∧ p1) ∨ (((p2 ∧ (p3 ∧ p2)) ∧ True) ∨ p4)) ∨ (p2 → (((True ∧ (False ∨ (p3 ∧ (p2 ∨ p4)))) ∨ True) ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135574010074114592584629439464 : ((((p3 ∨ (((p3 → ((False ∧ ((p4 ∧ True) ∧ p5)) → p2)) ∨ p5) ∧ p4)) ∧ p4) ∨ ((p2 ∨ (p2 ∨ p4)) ∧ p4)) ∨ ((p1 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643068064906918820223268772341 : ((((p2 ∧ (True → (((p5 ∧ p2) ∧ (p2 → p5)) ∧ (((False ∨ (p3 ∨ (p5 ∧ p4))) ∨ (p5 → False)) → ((False → p4) → p4))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51224054685698255054684322446 : ((((True → (((p2 ∧ p5) ∨ p1) ∧ p1)) → (p1 ∨ (False ∧ (p3 → (True ∨ (p1 → p5)))))) ∨ (((True ∨ False) ∨ (p2 ∨ p5)) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_82453321325130490139406403337 : (((p2 ∧ (p2 ∧ (((False ∨ (p5 ∨ (True ∧ (p1 → True)))) ∨ (p2 ∧ False)) → ((p2 ∨ p4) → p4)))) ∧ (p1 → (p3 ∧ (p4 ∨ p1)))) → p4) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((False ∨ (p5 ∨ (True ∧ (p1 → True)))) ∨ (p2 ∧ False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89145260158564261427940097460 : ((((p3 ∧ p5) → p2) ∧ (True ∧ ((((p1 → (p5 ∨ p2)) ∨ p4) → (p3 ∧ p1)) ∧ ((p3 → True) → ((p2 → (p1 ∧ p2)) → p2))))) → p1) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 → (p5 ∨ p2)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h10
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p2 → (p1 ∧ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h16 := h6 h8
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147090227885090876361558678559 : ((((p3 ∧ ((p4 → p1) ∧ p3)) → (p4 ∨ (p3 ∧ ((True ∨ True) ∧ ((p3 ∨ p1) ∧ (p5 → p2)))))) ∧ False) ∨ ((False → p2) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204148461022429250875976820063 : (((((p1 ∨ p2) ∧ p3) ∨ p2) ∧ p3) ∨ (((p4 ∨ (p5 ∨ ((p1 → ((True → (p1 → p4)) ∧ p4)) → p2))) ∨ (p1 ∧ True)) → (False ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216961567309080926531906281222 : (((p2 → (p5 ∧ p2)) ∧ p1) → (p5 → ((p2 ∧ ((p3 ∧ p3) → False)) ∨ (p3 → (((p3 ∧ ((p5 ∧ p1) → False)) ∨ (p1 ∨ p4)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151857278882365423639002196386 : ((((p4 → (True → (p5 ∨ True))) ∨ (p4 ∨ (p3 ∨ (p2 ∨ (True ∨ p2))))) ∨ ((p5 → (True → True)) ∧ True)) → ((False ∨ True) ∨ (p3 ∧ p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h12 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134846909907976200728392685457 : (((p4 ∨ ((p4 ∧ p3) → (p1 → (((((((p3 ∧ p2) ∧ p5) ∨ p4) ∨ False) ∨ False) → p2) ∧ (p4 → p5))))) → p2) ∨ (p2 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263163036476549118096740839892 : (True ∧ ((False ∨ (((((False ∧ p1) ∧ p1) ∨ p1) → ((False ∨ (p2 → ((p1 ∧ (p4 ∧ (p5 → p2))) → False))) ∧ p4)) → p3)) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351335959616341730184337193970 : (p4 → ((p4 → ((p2 → ((((p5 ∧ (p3 ∧ False)) ∨ (((p5 → (p2 ∨ p1)) ∧ False) ∧ p2)) ∧ p3) ∨ p4)) → p5)) → (p5 ∨ (p2 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → ((((p5 ∧ (p3 ∧ False)) ∨ (((p5 → (p2 ∨ p1)) ∧ False) ∧ p2)) ∧ p3) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51131627490051864626647014499 : ((((p3 ∨ ((p5 ∨ p4) ∨ (True → (True → (p5 ∧ ((p1 ∧ p4) → (p5 → p3))))))) ∨ False) ∨ ((p1 ∧ (True ∧ (p3 ∨ p3))) → p3)) ∨ p1) := by
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
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326966963654142974352612587752 : (True → ((((False ∨ p4) ∨ ((p4 ∧ p5) ∧ (p5 ∧ (((((p1 → p2) → p5) ∨ (False → (p4 ∧ False))) ∨ p3) ∨ p2)))) → (p1 ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
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
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140101966938938368933076912831 : (((p2 ∨ (p1 → ((((p5 ∨ ((True → p3) → (True ∨ p1))) ∨ p3) → p2) → (True ∧ (p3 ∧ p4))))) ∨ (True ∨ p5)) → (p1 ∨ (p5 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657667504090278851279821626902 : (((((p4 ∨ p3) → ((False → False) → (((p1 ∨ (p5 ∨ (p5 ∨ (p1 ∧ (p1 ∧ (p3 → p5)))))) ∨ p5) ∨ (p3 ∧ p1)))) ∨ (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148311466799743901434365731080 : (((p2 ∧ ((p4 ∧ p4) ∨ (((p2 ∨ (False → (True ∧ p2))) ∨ p2) ∨ (p5 ∧ p1)))) → (True → (p3 ∨ p3))) ∨ ((p2 ∨ True) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682080569800314150509441597465 : (((((((((p4 ∨ (p2 → p5)) → ((p3 → p2) ∨ True)) ∧ (p3 ∨ True)) → p1) ∧ True) → p1) ∧ (((p3 ∧ (p4 → p1)) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164686464877996993320503032646 : ((((p1 ∨ (p2 ∧ ((p3 ∧ (p2 ∨ ((p3 ∨ p3) ∧ p4))) ∨ (p2 → p1)))) ∧ False) ∨ False) ∨ (((False ∧ (p2 → p3)) ∨ (True ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185631396901877715424758418500 : ((True → (p3 ∨ (p4 ∧ ((p1 ∧ (p5 ∧ p1)) ∧ (p1 → p3))))) ∨ (p2 ∨ (True ∨ (((p1 ∧ p4) ∧ False) ∧ (((p2 ∧ False) ∨ p5) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612856693243459514718160121977 : (((((p2 ∧ (False ∨ ((p5 ∨ ((False → False) → (((True ∧ p5) ∧ (p3 ∨ (p5 ∧ p4))) → False))) ∨ (True ∧ p1)))) ∨ (False ∨ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262175396967133749549078779997 : (True ∧ (((p5 → (p4 ∨ ((((p2 ∨ p2) ∨ (False ∨ (p3 → p2))) → (False ∨ (p4 ∨ ((p5 ∨ (p4 ∨ False)) → p4)))) ∧ p1))) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178636160627427822896544867200 : ((((p1 → True) → ((p4 → p4) → True)) → (((p5 → False) → p5) → p3)) ∨ ((((p1 ∨ (False → p1)) → ((p1 ∨ True) ∧ False)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755546003383009658656839748270 : (((p1 ∧ ((p4 → (p4 ∧ ((p2 ∧ ((p2 → p1) ∧ (((p1 ∧ p1) → (p3 → p2)) ∧ True))) ∨ ((p5 ∨ p4) ∧ (p2 → p1))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746290067666370986353679626171 : ((((p1 ∨ p5) → (p1 → ((p5 → (p2 → (p2 ∧ (((p2 ∧ p2) ∨ (((True → (p1 ∨ p5)) → (p1 ∧ True)) ∧ p5)) ∧ p5)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134222373481995559927071092118 : ((((((True ∧ p1) ∧ (False → True)) → False) ∨ (False ∨ (p3 ∨ (p4 ∨ ((((p2 ∨ p3) ∨ p5) → True) ∨ p3))))) ∨ False) ∨ (p4 → (False ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112802594138455579760228819775 : ((((((True ∨ False) ∨ False) ∨ (p3 → p3)) ∨ (((False ∧ p1) ∨ ((False ∧ p1) ∧ (p5 → p5))) → ((p5 ∨ p4) ∨ p5))) → False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37173742074140405385610765877 : (((((p5 → ((p3 ∨ ((p1 ∧ True) → ((p5 → (p4 ∨ p2)) ∨ p3))) ∧ False)) → (p1 ∨ (((False → p1) → p4) ∨ False))) ∧ p5) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193069135378523203418127628621 : ((((p1 ∨ (True ∧ p1)) ∨ p5) ∧ (True → (False → p2))) → ((True ∧ (((p1 ∨ (p4 → False)) ∨ True) → (p1 → p4))) → (p5 ∨ (p5 ∨ p4)))) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : ((p1 ∨ (p4 → False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : ((p1 ∨ (p4 → False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130000607681307235679721552666 : (((((p1 ∧ p2) ∨ ((p4 ∧ p1) ∨ (False → (True ∨ True)))) ∨ (((True ∨ False) ∨ p3) ∧ (p3 ∨ p5))) ∧ (p2 ∨ True)) ∧ ((p4 ∨ p1) → True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191576772857597552631309408711 : ((p2 ∧ ((p1 ∨ ((True → p2) ∧ p3)) ∨ (p5 → p2))) ∨ ((((p2 ∨ p1) → p4) ∧ (p4 ∧ p1)) ∨ (p4 ∨ ((p5 → (p3 ∧ p3)) → True)))) := by
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
theorem thm_5_vars_65493556213611250297686775543 : ((p3 ∨ (p4 ∧ (((p1 → p2) ∧ ((((p1 ∧ p5) ∨ p3) ∨ ((((True → p3) ∧ p2) ∨ False) ∧ True)) → p1)) → (p3 ∨ (p4 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325797380065769273642634092744 : (p5 ∨ (p3 ∨ ((p1 ∨ ((((p1 ∧ (p5 → False)) → False) ∨ p5) ∨ (((False ∧ p3) → False) → (p4 ∨ (False ∨ (True ∨ (p1 ∧ False))))))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246239360042241195108651331879 : ((p4 ∧ p3) ∨ (p4 ∨ ((((p4 ∨ (p3 ∧ (((p5 → (False ∨ p5)) ∨ (True ∨ (False → False))) ∧ p1))) → p3) ∧ p1) ∨ (p5 → (p4 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



