variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68186188440090353832225181120 : ((p3 → ((((p1 → ((True → p1) ∨ ((False ∨ ((p5 → ((p4 → False) → p4)) → p5)) → True))) → False) ∨ ((p2 ∧ p1) → False)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231265201709516646292023028554 : (((p4 ∨ p5) ∨ p1) → (False ∨ (((p1 → False) → ((((p2 ∨ p1) ∧ (False → p1)) ∨ p5) ∧ False)) ∨ (p4 → ((p5 ∨ (p1 ∨ True)) ∨ p4))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617435184492512341196466525692 : (((((p4 → (((p3 ∨ p5) → True) ∧ (p3 ∧ p4))) → (p3 ∧ (((p2 ∧ ((p5 ∧ p2) → p3)) ∧ ((p4 ∨ False) ∧ p3)) → True))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_114946836275257368301306940188 : ((((p4 ∧ p2) ∨ (p3 ∧ ((p2 ∨ False) ∨ (((p2 → False) → True) → p2)))) → (p1 ∨ ((p4 ∨ (False → (p1 ∨ p3))) ∨ p4))) ∨ (p5 ∧ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76275608714907807094727328466 : (((((p5 ∧ (((p3 → ((p5 ∨ (p1 → False)) ∧ False)) ∨ p3) ∨ ((p4 ∨ (True ∨ False)) ∨ (p2 ∨ True)))) ∨ False) ∨ (p4 ∨ True)) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (((p3 → ((p5 ∨ (p1 → False)) ∧ False)) ∨ p3) ∨ ((p4 ∨ (True ∨ False)) ∨ (p2 ∨ True)))) ∨ False) ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624403696695608405967038699303 : ((((p3 ∨ (p3 ∧ ((((((((p4 ∨ p2) ∧ False) ∨ p5) ∧ p1) ∨ (p3 → (p1 ∧ (p1 → p1)))) → p1) ∧ (p2 ∧ p5)) ∨ p1))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117583024664483075220914026055 : ((p2 ∧ (True ∧ ((True → ((((False ∨ p2) ∨ ((p2 ∧ (False → p1)) → p3)) ∨ p4) ∨ (False → ((p2 → False) ∧ p1)))) → p3))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350914283217973314736128194317 : (p4 → (((((((True ∨ ((True → p5) ∨ p1)) → (p3 ∧ ((True ∧ p2) ∨ (p5 ∨ p4)))) ∧ p3) ∨ (p5 → p4)) ∧ p1) ∨ p1) ∨ (p1 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178780333008521828434078721381 : (((p4 ∨ (p1 ∧ p3)) ∧ (p2 ∧ ((True ∧ p3) ∧ (p4 ∨ (p3 ∨ p3))))) ∨ (p5 → ((p4 ∧ (p5 ∨ (p1 → p3))) → (p4 ∧ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590938521753580598085872765619 : (((((False → (p1 ∨ ((p5 ∧ (((True ∧ p5) ∨ ((((p3 → p2) → p1) ∧ p2) ∨ p1)) → p5)) ∧ ((False → p1) ∧ p1)))) → p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806265332180663570827461688573 : (((p4 → ((((p5 ∧ p4) → ((p1 → ((False ∧ False) ∧ ((p2 ∨ True) ∨ True))) → p3)) → (((p1 ∨ (True ∧ False)) ∨ False) → p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46765497009303650699586227364 : (((p2 → (p4 ∨ (p1 ∧ (p4 → (p1 ∨ (p5 ∧ (False ∧ ((p3 ∨ (True ∨ True)) → (False → ((p1 → True) → p4)))))))))) ∧ (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336248203158723534235878224157 : (p1 → (((p5 ∨ ((((p1 ∧ (p5 ∧ False)) ∨ (p5 → False)) → (p1 ∨ (p5 ∧ (p4 → False)))) → True)) → ((p5 ∧ (p3 ∧ p4)) ∧ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687843314530991701713288538692 : ((((((p1 ∧ p4) ∨ (((p4 ∧ p3) → (p1 ∧ False)) → p1)) ∧ ((True ∨ p5) → p4)) ∧ ((p3 → (p2 ∨ ((p5 ∧ p4) ∨ p2))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166441403301825754904930162027 : ((p2 ∨ ((p5 → (((p4 ∨ p3) → (False ∨ p5)) ∨ (p4 → ((p4 ∨ True) → p3)))) ∧ p3)) ∨ ((((False ∨ p1) → (p4 ∨ False)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687211132770727360747781035990 : ((((p5 → (p2 ∧ ((p3 ∨ (True → ((False ∨ p3) ∨ (False ∧ (True ∧ (False ∨ False)))))) ∧ p2))) → (p1 ∧ ((p1 → p5) ∧ (p1 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616377114113721319630414892805 : (((((p3 → ((((p3 ∨ ((p2 → p2) ∨ False)) → p4) ∧ True) ∨ p4)) ∨ ((p3 ∧ ((p4 ∨ (p2 ∨ p5)) ∨ (True → True))) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65656371093086603623845428014 : ((p4 ∨ ((True → ((p4 ∧ (((p4 ∨ (p3 ∨ (p1 → (p1 ∧ ((True ∨ p3) → (p5 → True)))))) ∨ p2) → (p1 ∧ False))) ∧ p1)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307425300856543780567328549101 : (p1 ∨ (p5 ∨ (((p3 ∨ (False ∧ False)) ∧ ((p5 → (p1 ∨ True)) ∨ (p5 → ((p2 ∨ (True → True)) → ((p4 ∧ False) ∧ (False → p5)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121230508786533794103197872106 : (((p1 → (p1 ∨ (((p1 ∨ p4) ∧ ((((p4 → p3) ∧ p5) → (p1 ∧ True)) ∧ p1)) → ((False → p4) ∧ (p4 ∨ p2))))) ∨ p1) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264786358213199247010188870519 : (True ∧ ((True ∧ p2) ∨ (p2 → (((p2 → p3) ∨ (p5 ∨ p1)) → (((True ∨ p3) ∧ ((True ∧ ((p4 ∨ p3) ∨ p1)) ∨ (p2 ∧ p1))) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39360863283323470450998021677 : (((p3 ∧ (((p2 ∨ (p4 ∨ (((False → (True → p4)) → p1) ∧ ((p1 → ((p5 ∨ p3) → p5)) → (p2 ∨ p2))))) → True) → p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157429197825034762252613311343 : ((((True → p5) → ((p2 ∨ p3) ∧ ((True → ((p2 ∨ p2) ∨ (True ∨ p4))) ∧ False))) ∧ (False → True)) ∨ ((p4 ∧ ((p1 → p4) ∨ p4)) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265719514306570271422297581462 : (True ∧ (p3 ∨ ((((p4 → p1) ∨ ((p2 ∧ True) ∨ p3)) ∧ False) ∨ (p4 ∨ ((False ∧ (p2 → (((p2 ∨ True) ∧ (p2 → True)) → p4))) → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758746673438334559503104514109 : (((p2 ∧ ((p5 ∧ (((((p2 → (((p3 → p3) → p4) ∨ p3)) ∧ (p1 ∨ (True ∧ p3))) ∨ (p2 ∧ (p3 ∨ p4))) ∨ False) ∧ p2)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185278856089610836051198887733 : ((p2 ∧ ((((p3 ∨ ((p3 → p5) ∧ p5)) → p1) ∧ p3) ∨ p2)) ∨ (((((True ∧ p3) ∧ ((p5 ∨ p3) ∨ False)) ∧ (p4 ∧ p2)) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162505610313921096313671711285 : (((p2 ∨ (((((p5 ∨ True) ∧ ((p3 ∧ (p2 ∨ p3)) ∨ p3)) → False) ∨ True) ∨ p2)) ∨ p2) ∧ ((p1 → ((False ∧ p1) ∧ (p3 ∧ False))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57838490756831986412135636922 : (((p5 ∧ (p5 ∧ p5)) → (((p2 ∨ (p4 → True)) ∧ (p1 → (((((False ∧ p1) → p4) ∧ (p5 → p5)) ∨ (p5 → False)) ∧ p5))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342000629885047899493260890962 : (p2 → ((((p1 ∨ p2) → False) → (((p3 → (p2 → ((p3 ∨ p4) → False))) ∧ ((p4 ∨ (p3 ∧ True)) → p2)) ∧ p1)) ∨ ((False ∨ p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311073647801049395712222178532 : (p2 ∨ ((p2 ∨ p3) ∨ ((p5 ∨ p1) ∨ (((((((p1 → p3) ∨ ((True → p2) ∨ p4)) ∨ p4) ∨ (p1 ∨ (p4 ∧ False))) ∨ p1) → p1) → True)))) := by
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
theorem thm_5_vars_47304654067047193427558462774 : (((((True ∧ p2) ∧ False) ∨ (p3 ∨ (((((True ∧ (False ∧ p4)) → p3) ∧ p3) → ((False ∨ p4) ∨ False)) ∧ (p5 ∨ p3)))) ∨ (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43840725397352458489727897763 : ((((((((p5 → (((p5 → p3) ∨ p5) → (False ∨ p4))) ∧ True) → ((p3 ∧ p4) ∧ p2)) ∧ (p4 ∧ False)) → p1) ∧ (p3 → p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43627114930732499115919728346 : ((((((((p3 ∧ (p1 → ((p1 ∧ (p2 → ((False → True) ∨ False))) ∨ (p3 → True)))) → p1) ∨ p2) → p2) ∧ (p2 → p4)) → p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116203383516695536493164849534 : ((((False → p2) ∧ False) ∨ ((((False ∧ p5) ∧ False) ∨ ((p4 ∨ ((False ∧ p4) ∨ p3)) ∧ (False ∨ True))) ∧ ((False ∨ p1) → p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141590619679651103584116459145 : ((((False ∨ False) ∨ p5) → ((p2 ∧ (False ∨ (True → (((True → p5) → (p1 ∧ (True ∧ p4))) ∧ p5)))) ∧ (p5 → p4))) → ((p5 ∧ p3) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ False) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715790587007343706104140013896 : ((((((p2 ∧ True) → p3) ∨ p5) ∧ (p4 ∨ ((p5 ∨ (p5 ∨ (((((p1 ∨ p2) → False) ∧ p4) → False) ∨ (p4 → True)))) ∧ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164858612339922953640979209667 : (((p1 ∨ (((True → p4) ∧ p2) ∨ (((p2 → True) → ((p1 ∧ p5) ∧ True)) → p3))) ∨ p4) ∨ (p4 → ((True ∧ (p5 ∧ p5)) ∨ (p4 ∨ p2)))) := by
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
theorem thm_5_vars_342289562933900778809500144580 : (p2 → (((((False ∧ p3) ∨ p4) → p3) ∨ (p3 ∨ (p1 ∨ ((p2 → (p2 → (p2 ∧ p1))) ∧ True)))) ∨ (((False ∨ p3) ∨ (p4 → p4)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115746978114099600148056614494 : ((((False ∨ p1) → (p1 ∨ (p3 ∧ p3))) → (((p4 ∧ ((((p3 ∧ p2) ∧ True) → True) ∨ p2)) ∧ (p4 ∧ False)) ∧ (p2 ∧ True))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2959756320897792912842088486 : ((p1 ∧ (p2 ∨ p2)) ∨ (((p1 ∧ (False → p2)) ∨ p5) ∨ (((p1 ∨ True) → p5) ∨ (p1 ∨ (p5 → (p5 ∨ (p4 ∧ (p5 ∧ p1)))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136074579937023073923744456042 : ((((p5 → True) → (((p5 ∨ True) → p1) → p5)) ∧ (False → ((p1 → False) ∧ (p2 → ((p4 ∧ p3) ∧ (p3 → p4)))))) ∨ ((p3 ∧ p4) → p4)) := by
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
theorem thm_5_vars_690548879722958581483816467656 : (((((p3 → ((True → (p3 ∧ p3)) ∧ ((False ∧ p5) → ((p1 ∧ p2) ∧ False)))) ∧ p4) → (((True ∧ ((p1 → p3) → p1)) → False) ∨ True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306488079741826151277261417331 : (p1 ∨ ((p2 → p1) ∨ ((((((p5 ∧ p2) → p4) ∧ (((p3 → p1) → ((p2 ∧ p5) → p1)) → False)) ∧ p4) ∧ (p2 → False)) → (False ∨ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 → p1) → ((p2 ∧ p5) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h15 := h7 h8
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308521141025699600884704296877 : (p2 ∨ (((p4 → ((((p5 ∨ False) → p5) ∨ p1) → (((True ∧ (p4 ∨ p5)) → False) ∨ p1))) → ((p3 → (p2 ∧ (p5 → False))) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85953075437525165010829781197 : (((((False ∨ p2) ∨ (p1 → (True ∨ (p5 ∧ p2)))) → p5) ∧ ((True ∧ p4) → ((p3 → (((p4 ∨ (p1 ∨ True)) ∨ p2) → p1)) ∧ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ p2) ∨ (p1 → (True ∨ (p5 ∧ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164562108883950581177859847742 : ((((((p4 ∧ p1) ∨ p2) ∧ p4) ∨ (p2 ∨ ((p2 → (p3 ∧ (p5 → p5))) → True))) ∧ True) ∨ (p2 ∨ ((p5 ∧ (p2 ∧ (p2 ∨ False))) ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354588384385334342461337488866 : (p5 → (((p3 ∧ (((p3 ∧ (((p3 ∨ True) ∧ p4) ∧ True)) ∨ False) ∧ (p4 ∨ ((((True ∧ p1) ∧ p5) ∨ (p5 → p4)) → p3)))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358677166671857300157013721924 : (p5 → (p4 → ((p1 ∨ p3) → ((p1 ∨ (((p2 ∧ False) ∨ ((p1 ∨ p3) ∧ ((p2 → False) ∨ (p1 ∨ (True ∧ (p1 → p3)))))) ∧ p3)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214790781996525039742604852283 : (((p1 ∨ p1) ∨ (False ∨ p5)) ∨ ((True → (p3 → (p3 ∧ p3))) → (((True → False) → (p2 ∧ (((p1 ∧ (True ∨ p4)) ∨ False) ∨ p5))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351839664204245265902124879619 : (p4 → ((((((p3 ∨ p2) → (p5 ∧ p4)) → p4) ∧ (False ∨ p2)) ∨ p3) → ((p1 ∨ (p1 → (p2 ∨ (False ∨ p1)))) ∧ (p3 → (False ∨ p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767287477094210422636487920705 : (((p5 ∧ ((((((p4 → p5) → p1) ∨ p1) ∨ (((True ∧ (True ∧ (p5 → p5))) ∨ (p5 ∨ False)) → True)) → ((p5 → p4) ∧ p4)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256331286666582315233306524686 : ((False ∨ p2) → (((p1 → p4) ∨ (((p3 ∧ ((((p5 ∧ (True → p3)) ∨ p5) → (p4 → p3)) ∧ True)) ∧ ((p2 → p5) ∨ True)) ∨ p2)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148652098776451107999143023567 : (((((False → p5) → True) ∨ ((p2 ∨ False) → True)) ∧ (((p2 → p4) ∨ False) → ((p2 → (p4 → p5)) → False))) ∨ (False → ((p4 ∨ p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737840232740926796274444390558 : ((((True ∧ p1) ∨ ((p2 ∨ ((((p5 ∨ (((p5 → p5) ∧ True) ∧ ((p3 → p4) ∧ (p2 → True)))) ∨ (True ∨ p1)) → False) ∨ True)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255686620492428439925177370380 : ((p5 ∧ p5) → ((((p2 → (p3 ∧ True)) → (p1 ∨ (True ∨ (p1 ∨ ((p2 ∧ False) → p3))))) ∧ p2) → (p5 → (((p1 → p3) → p1) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718668942281028413478899729907 : (((((p4 ∨ True) ∧ (p4 ∨ False)) ∨ (((p4 ∨ (p4 → (False → (p4 ∨ (p2 ∧ False))))) → ((p4 ∨ p1) ∨ (True → (True ∨ p1)))) ∨ p1)) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60816778219288142715855780022 : ((True ∧ (p4 ∧ ((((p5 ∨ (p5 → p4)) ∨ (p3 → p5)) ∧ (((p3 ∨ True) ∧ p5) → ((p2 ∧ (p5 → p5)) ∧ p4))) ∧ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174738869164724425871144652756 : (((True ∧ (p4 ∨ True)) → (((p4 → True) ∨ p4) ∧ (True ∧ ((True ∨ p2) ∨ p5)))) → ((False ∨ (((p1 ∨ (p5 ∧ p1)) ∧ p1) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37793060145154395529206392907 : (((((True → p1) → ((True ∧ (((((p5 ∨ ((False → p1) ∨ False)) ∨ True) → p2) ∨ (p3 ∧ p5)) ∨ (p1 ∧ p4))) → p2)) → p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218769913302743321797897293227 : ((p1 ∧ ((False ∨ True) ∨ p4)) → (((((((False ∨ False) ∧ (p2 → True)) ∧ p2) ∧ True) ∧ p2) ∨ (p2 → p1)) ∧ (True ∨ (p5 ∧ (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48622445122900672343538306193 : (((((p5 ∧ ((False ∧ False) → ((p5 ∧ (p2 ∨ (p5 → (p2 ∧ p3)))) ∧ p3))) ∨ p4) ∧ (p5 ∨ (False ∧ p2))) ∧ ((p5 → p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198317283801779873659232531399 : ((p1 ∧ (p4 ∧ (p1 → (p5 ∧ (p5 → p5))))) ∨ (p4 ∨ (((False ∨ (False ∧ (False ∧ True))) ∧ (p1 ∧ p3)) ∨ ((True ∧ (True → False)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37757413360057764065271958610 : (((((False ∨ (p3 → (p2 ∨ p4))) ∨ (p2 ∨ (p4 → ((p2 ∧ (True ∧ p3)) → (((p3 ∧ True) → p5) ∨ (False ∨ p2)))))) → p4) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684377715816755683003560301372 : (((((False ∨ (p2 ∧ (((p1 ∧ p2) ∧ p1) ∧ (p2 → p4)))) ∨ ((p2 ∨ (p1 ∧ False)) ∨ p4)) ∨ ((p3 ∨ (False → False)) ∨ (p5 ∧ False))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48982445530057167412283327532 : ((((((p1 → ((p5 ∧ False) ∧ p4)) ∧ p4) ∨ (p2 ∧ (p1 → (p4 ∨ ((True ∨ p2) ∨ (p2 ∨ True)))))) ∨ p1) ∨ ((p2 ∧ False) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211475582131944798480502809441 : (((p1 ∧ p2) → (p2 → p2)) ∧ (((((p1 ∨ (p4 → p3)) ∨ p3) ∨ p3) → (p3 ∧ ((p2 ∨ p1) → p2))) ∨ ((p4 → (p5 → p5)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136003106578179155447754905140 : (((p2 ∨ (p2 ∧ ((p4 ∧ (True → (False ∨ p5))) ∨ False))) ∨ ((p5 → (p5 ∧ True)) → ((p5 ∧ (p2 ∧ p2)) ∨ True))) ∨ ((p5 → True) → p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156882298676361213888518352632 : (((((((True ∧ p1) → p4) → ((True ∨ ((True → p1) ∨ p4)) ∧ (p2 → False))) ∨ p1) ∨ p3) ∨ p1) ∨ (((p4 ∧ p5) ∨ (p5 → p5)) ∨ p4)) := by
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
theorem thm_5_vars_50399721310875223526037882279 : ((((True → p5) → ((p2 → p5) → (p4 ∨ ((p5 → (True ∨ (p2 ∨ p1))) → (True → (False ∧ p5)))))) ∨ (p4 → ((False ∧ False) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54653442352891242101191262697 : (((((p3 ∨ (p1 ∨ p1)) ∧ (p1 → p3)) ∨ p1) → (p4 ∧ (p5 ∨ (((False ∨ (p2 ∨ (p1 ∧ (False → (p5 ∨ False))))) ∧ p5) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44001878163969012995312772489 : (((((p1 ∨ ((p1 ∨ (((p5 ∧ p1) ∨ False) ∨ False)) ∨ (p3 ∨ (((p4 → p5) ∨ p1) ∧ p2)))) ∧ (p4 → p5)) → (False ∨ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637359335148722244446428110441 : (((((p5 → (((((p3 → p3) ∧ True) → p5) ∨ p4) → (p1 ∨ p5))) → (p5 ∧ (p4 ∧ ((False ∧ False) ∧ (True → (p5 ∨ p4)))))) → p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((((p3 → p3) ∧ True) → p5) ∨ p4) → (p1 ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356256011472555192657554595810 : (p5 → ((((((p5 → (p1 ∧ p1)) → (True ∧ (p2 ∨ p4))) → True) → p3) ∨ (p3 → p5)) ∨ (True ∨ ((True → False) → (True ∨ (p4 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148220482719226283424295290366 : ((((p3 ∧ ((p1 ∧ p3) ∨ (((False ∨ p1) → ((False ∨ True) → True)) → p1))) ∧ p4) ∨ ((True ∧ p4) → p4)) ∨ (p2 ∨ ((p1 ∧ p3) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_52571149609991917104092428048 : ((((((False → (p3 ∨ (p5 ∨ p1))) ∧ p2) ∨ (True → p5)) ∨ (False ∧ p2)) ∨ ((((p3 ∧ (p3 → False)) ∧ p2) ∧ False) ∨ (p1 → True))) ∨ p1) := by
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
theorem thm_5_vars_52746945384834536452777370994 : ((((p5 ∧ ((False ∨ (True → p3)) ∧ ((p2 → p1) → (True → p5)))) ∨ True) → (p4 ∨ ((p1 ∧ (((p1 ∧ p2) → p3) ∧ p5)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228584382275572869642661550244 : ((p1 ∨ (p4 ∨ p3)) ∨ (((p5 ∨ (False → p5)) ∧ p3) → (p1 ∨ (((p3 ∨ p3) ∨ ((p4 → p2) → p2)) ∨ (((p1 ∨ True) ∨ p4) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315314023351770048031542852006 : (p3 ∨ ((True → ((p1 ∧ p5) ∧ p2)) → (p2 ∧ (((((p5 → p2) ∧ ((((p2 ∨ (False ∨ p3)) → True) ∧ p5) ∨ p3)) ∨ p1) ∨ p5) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305294428840608631213717313278 : (p1 ∨ (((p1 ∧ (((p5 ∨ (p5 ∧ (False ∨ False))) ∨ ((p2 ∧ p5) → (p2 → True))) → p3)) → p3) ∨ (((p4 ∧ p2) ∨ (p5 → True)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (p5 ∧ (False ∨ False))) ∨ ((p2 ∧ p5) → (p2 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178639269965225123124051927044 : (((p3 ∧ (p3 ∨ ((p3 ∨ p1) ∨ True))) → ((p5 → p1) → (p1 ∧ p5))) ∨ (((False ∧ (p5 ∨ True)) → (p1 ∧ (p3 ∧ (True ∧ p2)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158873321321358020709727302526 : ((False ∨ ((((p5 ∧ True) ∨ p3) ∨ p1) ∨ ((p1 ∧ (p3 ∧ p5)) ∨ ((True → (p5 → True)) ∧ p3)))) ∨ ((True ∨ ((p2 ∧ True) → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340889893920636364783497957284 : (p2 → (((((False ∨ (False → (p1 ∧ (True ∧ (p1 → p4))))) → True) ∧ (False → False)) → ((((p5 ∨ p4) ∧ p4) ∧ (p5 ∧ p3)) ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62410310618679110630350134285 : ((p3 ∧ (((p2 → True) ∨ (((False ∨ False) → p1) ∧ p1)) → (True ∧ (((p4 ∨ p3) ∧ (True ∨ False)) ∨ (False ∧ ((p1 ∧ p1) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353760053013284655407216147992 : (p4 → (True → (p2 ∨ (p2 ∨ (p4 ∧ ((True ∨ ((p3 → p2) ∨ p5)) → ((((p4 → p1) ∧ p2) → ((p3 ∧ p4) ∨ (p1 ∨ p2))) ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344343162574218408490096066310 : (p2 → (p4 ∨ ((((p3 → (p2 ∧ p1)) → p3) ∨ ((p3 → p2) ∨ ((p5 ∨ p2) ∨ ((p5 → p4) ∧ ((p1 ∧ (p5 ∧ p5)) ∧ p3))))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66786130881885041428316380215 : ((True → (False ∨ (((p2 ∧ ((((p1 ∨ p1) ∧ True) ∧ p4) ∧ p1)) ∨ (p1 ∧ p1)) ∧ ((p5 ∧ ((False ∧ p2) ∨ (p3 → p2))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347101730612487283129290347268 : (p3 → (((((p3 ∨ p3) → True) ∧ ((((p1 → p2) → p5) → False) → True)) → p1) ∨ (((True → p2) → (p1 → p1)) → (p4 ∨ (p4 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49283902783649019124862772207 : (((p4 ∧ (p3 ∧ ((True ∧ (p3 ∧ (p1 ∧ ((((p2 ∧ (p2 ∨ p2)) → p2) → p1) ∧ (p5 ∧ p3))))) ∨ True))) ∨ ((p5 → True) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218940540710232042787186405336 : ((p3 ∧ (p5 ∨ (False ∧ p2))) → (p3 → (((((p5 → p5) ∧ False) ∧ True) ∧ (False ∨ (False ∨ p5))) ∨ ((False ∧ (p2 ∨ (p1 ∧ p5))) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975973803438298613526222997625 : (((True ∧ (((((p2 → True) ∨ ((p4 ∨ p2) ∨ ((False ∧ True) ∨ (p4 ∧ p3)))) → False) ∧ (p4 ∨ (((p3 ∧ p4) ∧ False) → False))) ∧ p1)) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : ((p2 → True) ∨ ((p4 ∨ p2) ∨ ((False ∧ True) ∨ (p4 ∧ p3)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : ((p2 → True) ∨ ((p4 ∨ p2) ∨ ((False ∧ True) ∨ (p4 ∧ p3)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h13
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111657229898279359491216332231 : ((((p1 ∧ (((((p2 → p5) ∧ p2) ∨ (p4 ∨ (p2 ∧ (p4 ∧ (((p5 → p3) ∨ p2) ∨ p5))))) ∨ False) → False)) ∨ True) ∨ p5) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114203838300043577279442930518 : (((((p4 → True) ∧ (p2 ∨ p1)) ∧ (p3 → (p1 → ((p5 ∨ p1) ∨ ((p5 ∧ p1) ∨ (p2 ∧ False)))))) → (p1 ∧ (p2 ∨ True))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136739337551583099459453705900 : (((False ∨ False) ∧ (((p4 → (((((p3 ∧ p4) → p1) → p1) ∧ (False ∨ (p2 → p1))) ∧ p3)) ∧ (p2 → True)) → p3)) ∨ (p1 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118435932034783576209277298108 : ((p2 ∨ (p1 → (p4 → (p5 ∧ ((p2 ∧ (((((False ∧ p1) → p5) ∧ p3) → (p3 ∨ (p5 ∨ p2))) ∨ (p3 ∧ p1))) → p3))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112826141496816553611349074064 : ((((((p1 → p4) ∨ p4) → p1) ∨ (((((p5 → p2) → p2) ∨ p2) ∨ (p4 ∧ ((False ∨ p2) → False))) ∨ (p5 ∨ p5))) → p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733292246822063818313341459675 : ((((p3 ∧ p4) ∧ (True ∧ ((((p5 ∨ p5) ∧ False) → (((((p1 ∧ p3) ∧ p3) ∨ ((p4 ∧ p4) ∧ (p3 ∧ p5))) ∧ p4) ∨ True)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148389396959191767230959074922 : ((((True → False) ∧ (True → (True ∨ (((p5 → p1) ∨ p1) → (p2 ∨ p4))))) ∨ ((p2 ∧ (p5 ∧ p4)) ∨ p5)) ∨ ((p4 → True) ∧ (False → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793178227112620869895226503197 : (((True → (False ∧ (((False ∧ ((p3 ∧ False) → p5)) ∧ (((((p3 ∧ p4) ∧ p4) ∧ ((False ∨ p4) → p1)) ∧ (False ∧ p5)) ∧ p2)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323997990235645472292562800074 : (p5 ∨ (((p4 → p5) ∧ (p2 → ((((p4 → p1) → p4) ∨ (p1 ∧ True)) ∨ False))) ∨ ((False ∧ (p2 ∨ (p2 → (p2 → (p5 → False))))) → p3))) := by
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
theorem thm_5_vars_704974667898534596893483721106 : ((((True → (False → (((p1 → p3) ∧ p1) ∨ (p2 ∧ p2)))) → (((True → (((p3 ∧ p2) → False) ∨ ((p5 → p4) ∨ p2))) → p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



