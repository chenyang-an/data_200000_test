variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184722455588565144496408396982 : (((False ∨ (((p2 ∨ p5) ∨ p2) → p2)) → (p1 ∨ (p2 ∧ True))) ∨ (((p3 → False) ∧ ((((False → True) ∧ p5) → p1) ∧ (p3 ∧ p5))) → p5)) := by
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
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149480626804497827622902522090 : ((False ∧ (True → ((p1 ∧ (False ∧ (p5 ∧ (p3 ∨ (((p1 ∨ True) ∧ p4) ∨ (p5 ∨ p1)))))) ∧ (False ∧ False)))) ∨ (((p4 ∧ p3) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158351066684643249134532279108 : (((p5 ∧ p4) ∧ ((False ∧ p3) ∧ (p4 ∧ ((p4 ∧ p5) ∧ (p4 ∨ (p1 → ((False ∨ p4) ∨ p2))))))) ∨ (((p5 ∧ (p5 ∨ False)) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767359051393495462819184964326 : (((p5 ∧ (((p5 ∨ True) ∧ (p5 ∧ (p4 ∧ ((p4 ∧ (((False ∧ False) ∨ p1) ∧ p1)) → ((((p1 ∨ p1) → p1) → p2) → p5))))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68640164275905626908451712877 : ((p4 → ((((((((p2 ∨ (p3 ∧ p4)) ∨ False) ∨ (p2 ∧ (((p3 ∨ True) → (p4 → p3)) ∨ p5))) ∨ p1) ∨ p4) → False) ∨ False) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62367064481657504961218515927 : ((p3 ∧ ((p3 → (((True ∧ False) ∧ ((p4 ∧ p4) ∨ (p4 → (False ∧ (p5 ∨ False))))) ∧ p2)) ∧ (p4 → (False ∨ (p2 → (False → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674869059288213535167376154655 : (((((((p2 ∨ False) ∨ ((((p5 ∨ ((True ∨ p1) ∨ True)) ∨ (p1 → True)) ∧ p1) ∨ p4)) ∧ p3) ∧ p5) ∧ (True ∧ ((p3 ∨ False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755632390819042824437085993642 : (((p1 ∧ ((((True ∧ p2) ∨ ((p3 ∧ (((p1 → p5) → p1) ∨ (p3 → (True ∧ p1)))) ∧ ((p4 ∧ p1) ∧ False))) ∧ (p5 ∨ p4)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191481919332905193870626005960 : ((True ∧ ((p2 → (False ∨ p5)) ∧ (p3 → (p3 → False)))) ∨ ((True → ((p1 ∨ ((True → (True → False)) ∨ (True → False))) → p5)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124111618688247071796832068714 : ((((((p1 ∧ p3) ∧ (False ∧ p1)) ∨ p5) → (False ∨ False)) ∧ (((((p2 ∧ (True ∨ p2)) → p2) ∨ p5) ∧ p1) ∨ (p4 → p2))) → (p5 → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (((p1 ∧ p3) ∧ (False ∧ p1)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (((p1 ∧ p3) ∧ (False ∧ p1)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h19 : (((p1 ∧ p3) ∧ (False ∧ p1)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h19
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344186008802712596237158661598 : (p2 → (p1 ∨ (((((p1 → False) ∨ p1) ∨ (p5 → (p1 ∧ (p4 ∨ (True ∧ True))))) → p1) ∨ ((p1 → ((p2 ∧ p1) ∨ (p4 ∧ True))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348892684723838465725380235962 : (p3 → (p2 ∨ (p1 ∨ (((False ∨ ((((p1 ∨ (True ∧ p4)) ∧ p1) ∨ p3) ∧ (False → ((((p2 ∨ False) ∨ p3) → True) → p3)))) → p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324895390033441345255641045305 : (p5 ∨ ((p1 ∧ False) ∨ ((False ∨ p4) ∨ (((p1 → ((p4 → (p3 ∨ p2)) ∨ p2)) → ((((p3 ∧ p1) ∨ (p2 → True)) → p3) ∨ True)) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111604956895317967945422571945 : (((((False ∧ (False ∧ ((p2 ∨ (p5 ∧ False)) ∨ ((p5 ∨ (p5 ∧ False)) → ((False → p5) → (True ∧ p4)))))) ∧ False) ∨ True) ∨ p3) ∨ (p1 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14708783294217235543987626155 : ((((p4 ∧ ((p5 ∧ (((p5 ∨ (((p4 → (p2 → (False ∧ p5))) → False) ∧ p3)) ∧ p1) → False)) ∧ p2)) ∨ (True ∨ True)) ∨ (p2 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152151181380368881800811061664 : ((((((p1 → p4) → p5) → True) ∨ (p2 → p4)) ∨ ((((p3 → False) → p4) → ((False ∨ p1) ∧ p3)) → p3)) → ((p2 ∧ p3) ∨ (False → p1))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214837451377411645597772689811 : (((p5 ∨ p3) ∨ (False ∧ p1)) ∨ (p2 ∨ (((((p4 ∧ p2) ∧ (p4 ∧ ((p1 ∧ p3) ∧ ((p5 ∨ True) ∧ p1)))) ∨ (p4 → p1)) ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86599716629481705375247521383 : ((((p3 → ((False → (p2 ∧ p4)) ∨ p2)) → p5) ∧ (p3 → ((((p1 ∨ True) ∧ ((False ∨ True) ∨ p1)) ∧ False) ∨ (p5 ∧ (True ∨ True))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((False → (p2 ∧ p4)) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159690464357467979001492428667 : ((((p2 → (((((p4 ∨ p1) → (p4 ∧ (p4 ∧ p3))) ∧ True) → p5) ∨ True)) ∨ (p5 ∨ p2)) ∨ p4) → ((((True ∧ True) ∧ p1) ∨ p5) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307304169984175182975787779897 : (p1 ∨ (p3 ∨ (((p4 → p3) ∧ ((p1 ∧ p5) → ((((((p4 ∨ ((p3 ∨ p3) ∨ p1)) ∨ False) → True) ∨ (p3 ∧ False)) ∧ p4) ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344878559198860731580595327989 : (p2 → (p5 → (p3 ∨ ((((((p1 ∧ p5) ∨ (p5 ∧ p1)) → p3) ∨ p1) ∨ (((p5 ∧ (p2 → True)) ∧ p4) ∧ (p5 ∧ (True → p3)))) ∨ True)))) := by
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
theorem thm_5_vars_179697965298392151519739891333 : ((((((True ∧ ((p3 ∧ (p4 ∨ False)) → p3)) ∧ p1) → p3) ∨ True) ∧ True) → (((False → p1) ∧ p3) ∨ (p4 ∨ (p2 → (p3 ∨ (p1 ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773693156289402063322002971639 : (((False ∨ (((((p1 ∨ (p4 ∨ (((p4 ∨ p1) ∧ False) ∧ p2))) ∧ False) → (p2 ∨ ((p3 ∧ (p2 ∨ p5)) ∧ (False ∧ p1)))) ∧ p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2181269260816584817262248703 : ((((((p1 → ((True ∧ p4) → ((p1 ∨ False) ∧ p2))) → p3) ∧ False) → p2) → False) ∨ ((False ∧ p3) → ((p1 ∨ (p2 ∧ p3)) ∧ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227216802409884341154170570045 : (((False → True) → p2) ∨ (((((False ∧ (False → (p1 ∧ p2))) ∧ p5) ∨ (p4 → True)) → (p5 ∧ ((((False ∨ p1) ∧ False) → True) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52643267828456064822549365837 : ((((p2 ∨ p5) → (((p5 ∧ (((False ∨ p1) ∨ True) → p3)) ∧ False) ∧ p5)) ∨ (p4 ∨ (p5 ∨ (((p4 ∨ p3) ∧ p3) ∧ (False ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137777935025389883595978263596 : ((p2 ∨ (((p2 ∧ p1) ∧ ((p2 → True) → p3)) ∨ (((True ∧ False) ∨ (((False ∨ p3) ∧ p1) ∧ p3)) ∨ (p1 → True)))) ∨ ((p4 → p2) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40982433900297108499585315168 : ((((False ∧ (((p4 ∧ True) ∨ False) ∨ ((p1 ∨ (p1 → (p4 → (p5 ∧ (p5 ∧ (p5 → (p2 ∨ p5))))))) ∨ False))) ∨ (p1 → p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39981539390346145414989188771 : (((p4 → (p4 → (((p3 ∨ p5) ∨ (((p1 ∧ p1) ∨ True) ∨ p2)) → (((p2 ∨ p1) → ((p1 ∨ (True ∨ True)) → False)) → p2)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174544688980680646433464341571 : (((p4 ∨ ((p1 → p1) ∧ (True ∨ True))) → ((p2 ∨ (True ∨ (p3 ∨ p1))) → p4)) → (((p3 ∨ (p1 → ((p2 → p3) ∨ p5))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788504125413163126625872418407 : (((p5 ∨ ((p4 ∧ (p5 → (((((p1 ∨ True) ∧ ((False ∨ (p5 → p5)) ∨ True)) → p1) ∨ (((p3 ∧ p2) ∨ True) ∧ False)) ∧ True))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134773355311090830544390844481 : (((True ∧ (p4 ∨ ((p1 ∨ p4) ∨ ((((p4 → (p3 ∧ p1)) → (((False ∨ p5) → p4) → p1)) ∧ p2) ∧ True)))) → p4) ∨ ((True ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724746860409160802536488355484 : ((((p3 ∨ (p1 ∨ False)) ∧ (p3 ∨ (True ∧ (((p5 → p4) ∧ (False ∧ ((((p1 → True) ∨ p5) ∧ ((p2 ∧ p5) → p1)) ∧ True))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136374776744084277871334563542 : ((((p3 ∧ (p3 ∨ p4)) → p4) ∨ (((p5 → ((p1 → False) → p3)) ∧ p4) → ((p3 ∨ (p1 ∧ p4)) ∧ (False → p1)))) ∨ ((False ∧ p4) → p1)) := by
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
theorem thm_5_vars_745636634890556921397746456610 : ((((True ∨ p3) → ((((False → ((False → p3) → ((p4 → p4) → (p3 ∨ True)))) → (p1 ∧ (True ∧ (p4 → p4)))) ∨ p3) → (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326858051888956193720013818611 : (True → (((p4 → ((p3 ∨ p2) ∧ ((((p3 → p5) ∧ p2) ∧ (p1 → p4)) ∧ ((False → p3) → (((False ∧ True) ∨ p1) → p3))))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41881226339405419544375491544 : ((((p5 ∧ (p5 → p3)) ∨ (((p4 → True) → p3) ∧ (p2 ∨ (p2 ∨ (((True ∧ (True ∨ p4)) ∨ (True → True)) ∧ (p5 ∨ p4)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173214148440364301373762444209 : ((p5 ∨ ((p2 ∨ p2) ∨ (p1 → (False ∨ ((p1 ∧ (p3 ∨ p3)) ∨ (True → False)))))) ∨ ((p5 ∨ p5) → (((False ∨ (p5 ∧ False)) → p1) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214719464986033008181877732994 : (((p1 ∧ p5) ∨ (p1 ∧ p4)) ∨ ((((((p5 ∧ p3) → (p5 ∧ p4)) ∨ (p3 → p4)) → (True → ((p1 → (p4 ∧ True)) ∨ True))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311821750436769724936523608179 : (p2 ∨ (p1 ∨ ((True ∧ (p3 → ((p2 → True) ∧ (p1 ∨ (((p2 ∧ p2) ∨ (False → p2)) ∨ (p5 → False)))))) ∨ (((False ∧ True) → p4) → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228995750376308541412770606678 : ((p5 ∨ (False ∧ p4)) ∨ ((p3 ∨ p3) ∨ (False → (((p5 ∧ ((p3 → p5) ∧ (False → p3))) ∧ (((True ∨ True) → True) → (p1 ∧ p2))) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764650119783112503992529790949 : (((p4 ∧ (((p5 → (p2 → False)) ∨ ((((((p5 → p3) ∧ ((p4 ∨ p3) ∧ (False → (p1 → p4)))) → p5) ∨ p3) → p5) → p1)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112447571683787147967566419186 : (((((p1 → ((p5 → p1) → (p5 → (((p1 → p3) ∧ (((False ∨ True) ∨ p2) ∧ p2)) ∨ (p1 ∨ p3))))) → True) ∨ p5) → p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180157395111347912554890497628 : ((((p4 ∨ (p4 ∧ (((p2 ∧ True) ∨ True) → False))) ∨ (p5 ∨ p2)) → p4) → ((True → (p5 ∧ p3)) → ((p1 ∨ ((p3 ∨ p2) ∧ p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303922198340634609330406214215 : (p1 ∨ (((p1 ∨ ((p1 ∨ p5) ∨ (p1 → (p2 → (p2 → False))))) ∨ ((((((False ∨ False) ∨ False) ∧ p4) ∨ (False ∧ p3)) → False) ∨ p1)) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327829209079095907641201227456 : (True → ((((p4 → True) → ((p1 ∧ (p2 ∨ (((p1 ∨ ((p4 → p5) → p5)) ∧ p4) ∨ (p2 → p4)))) → p1)) → (p3 ∨ p1)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48991829156583245124946785843 : ((((p1 ∧ (((((p4 → p1) ∧ (((p4 → p4) → (True → p3)) → p1)) → (p2 ∧ True)) → p3) ∧ False)) ∨ p2) ∨ (p5 ∨ (p4 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663767896589981170762528568731 : ((((p2 ∧ ((((((p3 → p1) ∧ (False ∧ (True ∨ True))) → ((p1 ∧ p5) ∧ (p4 ∧ True))) ∨ p2) → False) ∧ (p4 ∨ p1))) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54405105607268307121303742258 : (((((p3 ∧ False) ∨ ((True → p4) ∨ True)) ∧ p5) ∨ (p4 ∨ ((p1 ∨ (p1 → (True ∨ p1))) → (p1 → (p5 ∨ ((p3 ∧ p5) → p3)))))) ∨ p1) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56561031121947183513184087886 : (((p4 ∨ (p1 → (True → False))) → (((p4 ∨ (p2 ∧ ((p1 → False) ∧ p2))) ∨ (p1 ∧ p4)) ∧ (((p3 ∧ (True ∨ p3)) → False) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300495402006281279883818003740 : (False ∨ ((((True ∧ (True ∧ (False → p3))) → (((p1 ∨ (p2 → (p1 ∨ False))) → p5) ∧ (False ∧ p4))) → False) ∧ ((p2 ∨ p5) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (True ∧ (False → p3))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171390343788913272642841151758 : ((((p4 → ((p3 ∨ (p3 ∨ p2)) ∨ p3)) ∧ ((True ∧ (p4 ∨ p4)) ∧ True)) ∧ p3) ∨ (p5 ∨ (False → ((p4 ∨ p2) ∧ (p3 → (p1 ∨ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790308267122177011770556270500 : (((p5 ∨ (p2 ∧ (False ∨ (((p5 → (False ∧ (False → (p5 ∧ p5)))) ∨ p4) → ((p1 ∨ (p5 ∧ ((p4 ∨ (p5 → p4)) ∨ p3))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157724195099704666539263526264 : (((True ∧ (((p4 → p2) ∧ (False → p4)) ∨ (True → ((True → p4) ∧ p2)))) → ((p2 → p2) ∧ p1)) ∨ ((((p4 ∧ p1) → p4) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356623611143635256080616265810 : (p5 → (((p3 ∨ (False ∧ (p3 ∨ p3))) ∨ (False ∨ True)) ∨ (True ∨ (False → ((p1 → True) ∧ ((False → (p2 → p5)) ∧ ((True → p4) → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42249959300923583489920756235 : (((p1 ∧ ((((False ∧ (False ∨ (((((((p3 → (False ∧ False)) ∨ True) → p4) → p1) → True) ∨ p2) ∧ False))) ∨ p3) ∨ p3) ∧ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324398589505690873871620990577 : (p5 ∨ ((((True ∧ (p4 → True)) ∨ p2) → True) → (p3 → (p3 → (((p5 ∨ (p1 → True)) → (p5 ∧ ((p5 ∧ (p3 ∨ p4)) ∧ True))) → p5))))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225410948400888707830224955703 : (((p3 ∨ False) ∧ p1) ∨ (((((p4 ∨ True) → ((True → (p4 → ((p5 → ((p2 ∧ (p2 → p2)) ∨ p5)) ∨ p1))) ∨ p4)) ∧ p1) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313035866214937065944336144496 : (p3 ∨ ((((p3 ∨ ((p2 ∨ p3) ∨ (((p1 ∨ False) ∨ (p3 ∨ True)) ∧ (((((p1 ∨ False) ∧ p2) → p1) → True) → p5)))) ∨ p5) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104488851766254350449411750148 : (((((True ∨ (((p2 ∨ p5) → p2) → ((p4 ∧ False) → ((False ∨ True) → True)))) → ((p4 ∨ p1) → p2)) ∧ p1) ∨ (p2 → p2)) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313099707490181539401919045923 : (p3 ∨ (((p1 ∨ (((p5 → (False ∧ p3)) → p1) ∧ ((p3 → (True → ((True → p2) ∧ (p5 ∧ False)))) ∨ (p2 ∧ True)))) → (p3 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126724371207808354925481010666 : ((p4 ∧ ((((False → p4) → (p3 ∧ p2)) ∧ p3) ∧ (p3 ∧ (((p2 ∨ (((True ∧ (True ∧ False)) ∨ False) ∧ False)) → p3) → p3)))) → (True ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56868276180689947380795343368 : (((p1 ∧ (p5 ∧ False)) ∧ (True ∧ (((p4 ∨ (p3 ∨ (p3 → p5))) → (p5 → (((p1 ∧ p1) ∨ p2) ∧ p1))) ∨ ((False → p1) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157820547793345202953111628219 : ((((((True → p1) ∧ True) ∨ p1) ∨ (((p4 → p3) ∨ p5) ∨ p3)) → (p5 ∨ ((p4 ∧ p2) ∨ True))) ∨ (((True → p4) ∧ p3) → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731252094752640209167366930227 : ((((p3 ∨ (False → p5)) → (p1 → (False ∧ (p2 ∧ ((((p4 ∧ (p5 ∧ True)) → ((p3 ∧ p1) ∨ False)) ∧ p5) ∧ (p4 → (p4 → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50442981458959726276600629940 : (((p1 ∨ ((((((p1 ∧ p1) ∨ p4) ∧ p2) → (False ∨ True)) ∧ (((True → True) ∨ p5) ∧ p3)) ∨ p1)) ∨ (p5 ∨ (p5 → (p3 → p3)))) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121234955941008880512275418405 : (((p2 → (((False ∧ False) ∧ ((p4 ∧ (True ∧ p4)) ∨ ((((True ∧ (p1 ∨ p1)) → False) ∧ (p5 → p3)) ∧ p2))) → p4)) ∨ p3) → (p3 ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138428751006357102320409022291 : ((p5 → ((((p1 ∨ p2) ∧ (((((p1 → p2) → p2) ∨ True) → (p4 ∨ p5)) ∧ p3)) → p2) ∨ ((False ∨ p4) ∨ p2))) ∨ (p4 → (p2 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258313718152082275304867259708 : ((p5 ∨ True) → ((False ∨ p5) → ((False ∨ (False ∨ ((p2 ∧ (p5 ∧ (p5 ∨ p5))) ∨ ((p3 → p3) → ((p2 → p5) ∨ (p5 ∧ False)))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623603722039689953567171406870 : ((((False ∨ (p3 ∨ (((p4 ∧ (((p2 → (p1 → (True ∧ False))) → p5) → (p1 → p5))) ∨ (p3 → True)) ∧ (p5 → (p3 ∧ p1))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_659192254464467937117639460117 : ((((p3 → (p4 → ((True → (p3 ∧ (p5 → (True ∧ (p5 → ((False ∨ True) ∧ p4)))))) → (((p4 ∧ False) ∨ p5) ∨ p2)))) ∨ (p3 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_609123352783173062265973700557 : (((((((p2 → p1) → ((False ∨ p3) ∨ p5)) → ((p3 → p4) ∨ (p5 ∧ (((((p5 ∨ p5) ∧ p1) ∨ p4) ∨ p2) ∧ p5)))) ∨ p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218560944522324579859717435217 : (((False → p1) → (p5 → p3)) → (((p1 ∧ (((True ∨ (False ∨ p2)) → ((p4 ∧ p5) ∧ p2)) ∨ False)) → (p2 ∧ (p1 → (True → p3)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (False ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ (False ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h19
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166279206777408761086214124580 : ((p4 ∧ ((((((True ∨ (False ∨ p1)) → (p3 ∨ (p2 ∨ p4))) → p5) → p1) ∧ p5) ∨ p1)) ∨ (True ∧ (p2 → ((p5 → (p5 ∨ p3)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42222163676903407729756625366 : (((False ∧ ((True → ((p3 → (p5 ∨ p4)) → ((True ∧ ((True → (p5 → (False ∨ p5))) ∧ p4)) ∨ (True ∨ p4)))) ∧ (p2 ∨ p4))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49395317138981083580073010996 : ((((((True ∨ True) → (False ∧ (p1 → (p2 ∧ (p3 → (False ∨ (p4 ∧ False))))))) ∧ (p1 ∧ (False → p1))) ∧ p4) → (p1 → (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647479242329127135903417170813 : ((((p4 → (False → ((p5 → (False ∧ (True ∧ ((((p4 → (p2 ∨ ((p4 → p5) ∨ p1))) → (True ∨ p3)) ∨ False) ∧ p1)))) → p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350301432534450830086348391340 : (p4 → ((p2 ∨ (((p2 → p4) ∨ p2) → (((p5 ∧ p4) ∧ (p5 → (p1 ∧ ((True ∧ (p4 → p5)) → False)))) ∧ (p4 ∨ (False ∧ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792153654511986778248623556611 : (((True → ((((p5 → (True ∨ p3)) ∧ p3) ∨ ((p5 ∧ (((p4 ∧ p1) → (p5 ∧ p5)) ∨ (p3 ∧ False))) → True)) → (p4 → (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205838574484821342449662805127 : (((p1 → p1) → ((p4 ∧ p3) → False)) ∨ ((((p3 ∧ p5) ∧ ((False ∨ (p1 → p1)) → (p2 ∧ (p5 ∧ p2)))) ∨ True) ∨ (p5 → (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147139254959108771379909052365 : (((False ∧ ((p5 ∧ ((p4 ∨ ((p5 ∧ ((False ∧ p4) ∨ p2)) ∧ (p1 ∧ p5))) ∧ (p2 ∨ p2))) ∧ False)) ∧ p3) ∨ (p4 ∨ ((p1 → p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734035976998413606345668595560 : ((((True ∨ p2) ∧ (((p3 → p4) → False) ∨ ((p2 → (p1 ∧ (p1 → p3))) ∨ (False ∨ (True ∨ ((p5 ∧ ((p1 ∧ True) ∨ True)) ∨ p1)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_147920357601778426506927693944 : (((((((p2 ∧ p4) → ((p5 → (p2 ∧ p4)) ∧ True)) ∧ p5) ∨ True) → (p3 → (p5 → p1))) ∧ (p5 ∨ p5)) ∨ ((p1 → True) ∧ (p1 → True))) := by
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
theorem thm_5_vars_302570959394948185483069393513 : (False ∨ (p1 ∨ (((True → (((False ∧ (False → p2)) → (p1 → p4)) ∧ ((p3 → p3) ∨ (p1 ∨ p5)))) → (p3 ∧ (False → p3))) → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (((False ∧ (False → p2)) → (p1 → p4)) ∧ ((p3 → p3) ∨ (p1 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140810252220314078386828548995 : (((p4 → (p2 ∧ ((p5 ∨ ((p5 ∨ (True ∨ p4)) → p5)) ∨ False))) ∧ (p5 ∧ ((p1 ∧ (p2 → True)) ∨ (p4 ∧ p4)))) → (p2 ∨ (p5 ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735702053209514405158575105164 : ((((p5 ∨ p2) ∧ (p1 → (p4 ∨ (p4 ∧ ((False ∧ (p2 ∨ ((p4 ∨ p5) ∧ ((p1 → (p5 ∨ ((p3 ∧ p1) ∧ True))) ∨ False)))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114703224040579709160015588758 : ((((((p5 → (p1 ∨ ((p5 → (p2 ∨ p2)) → (p5 ∨ p4)))) ∧ False) → True) ∨ False) → ((p1 ∨ (p2 → False)) ∧ (p5 → p5))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299275686382029809784571483160 : (False ∨ ((((p4 ∧ (p4 ∨ ((((p1 → (p3 ∧ p5)) ∨ p5) → p1) ∧ False))) ∨ p5) ∧ (p2 → (((p1 → (p4 ∨ False)) → p1) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263827581963218574910063293657 : (True ∧ ((((p2 ∨ (p4 → (p3 ∧ (False ∧ ((p4 ∧ p1) ∧ p4))))) → p1) ∨ (p1 ∨ True)) → ((p3 ∧ (p5 ∨ p5)) ∨ ((p3 ∨ True) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_350241171439693246091017423384 : (p4 → (((p5 → True) → (((True → True) → (p5 → (True ∧ p4))) ∧ (((p5 ∨ True) → (p5 → (p2 ∧ p1))) → ((True → p1) ∧ p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657347412620432571566347184366 : (((((p2 ∨ p3) ∧ ((((p1 ∧ ((p4 ∧ (p5 ∧ (True → p3))) ∨ (p4 ∨ p4))) → p1) → p5) → ((p2 → False) ∨ p5))) ∨ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256103459421752404971916667245 : ((True ∨ p5) → (((True ∧ ((p5 ∨ False) → (((((p3 ∧ p5) → True) ∧ p3) ∨ (p2 ∨ (p2 → p2))) ∧ p2))) ∨ (False → p2)) ∨ (p4 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259301949094757917424344552744 : ((False → p1) → (p4 → ((p1 ∨ (p5 ∨ ((False → False) ∧ ((p3 ∨ False) ∧ (p4 ∧ p3))))) ∨ (((False → (p1 ∧ (p2 ∧ p3))) ∧ True) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40373380172541634649994466076 : (((((p3 → ((False ∨ ((p2 → (p4 → ((p2 ∧ (p5 ∨ p1)) ∨ (p2 ∧ (False → (p5 ∨ p4)))))) ∨ p3)) ∨ True)) → False) ∨ p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698734956644034633799404297768 : (((((False ∧ p2) ∨ (((((p2 ∧ False) ∧ p1) ∧ p1) → p1) → p3)) ∨ ((p5 → ((False ∨ True) ∨ True)) ∨ (True ∧ ((p2 ∨ True) ∨ p1)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215525049596432397048826170768 : ((p4 ∧ (p5 ∧ (p1 → p2))) ∨ (((p1 ∧ p1) ∨ ((p1 ∨ p5) ∨ ((((p5 ∨ ((p5 ∨ p3) → (p3 ∧ True))) ∧ False) ∧ p1) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61126176879555212625816327684 : ((False ∧ ((p2 ∨ ((p4 ∧ True) ∧ (p1 → ((False ∧ p2) ∨ False)))) → (((p4 → p2) ∨ ((p5 ∧ p3) ∨ (p3 ∨ p2))) → (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232478447454752908390617964671 : ((True ∧ (p4 ∨ False)) → (((p2 → True) ∧ (p4 → ((p2 ∧ (p5 ∧ (((p4 ∧ p5) → p1) → (p5 ∧ p2)))) ∨ (p5 → (p4 ∧ True))))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4039630961578105068879292545 : (p2 ∨ (((p3 → p2) ∧ (p3 ∧ (p2 ∧ ((p2 ∨ (((p1 ∧ p2) ∧ p5) → ((p3 → p3) → False))) → False)))) ∨ ((p4 ∧ p3) → p4))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350993995949788633589985559508 : (p4 → ((p2 ∧ (False ∨ (p4 ∧ (p5 ∨ (True → (False ∨ ((p3 ∧ p3) ∨ ((p3 → p2) → (False ∧ (p3 ∧ (True ∨ p3))))))))))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



