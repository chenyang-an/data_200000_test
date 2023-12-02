variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258977973964806211072959058915 : ((True → p3) → ((True ∧ p3) ∧ ((((((p1 → (p2 → p1)) ∨ (((p2 → False) ∨ p3) ∨ (p1 ∧ p3))) → p5) ∨ p2) ∧ (p3 ∧ False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137212276993396723369476873792 : ((False ∧ (p5 → (((((p2 → (p1 ∨ False)) → p2) → (p4 ∧ p5)) ∨ ((p5 → ((p4 ∨ p1) → p2)) ∨ False)) ∧ False))) ∨ (True ∧ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118416796495473652530615020732 : ((p2 ∨ (p3 ∧ (False ∨ (((((p4 → (p1 ∨ True)) → (p2 ∧ ((p2 ∧ p1) ∧ p1))) ∨ p2) ∧ False) ∨ (p4 ∧ (False ∨ True)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357346612617692007508949927953 : (p5 → ((p3 → False) ∨ ((p2 ∧ (p5 ∧ (False ∧ p1))) ∨ (((p2 → False) ∧ (((p3 → ((True → p1) ∧ p4)) ∧ p4) → False)) → (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116495859126939643951812550457 : (((p3 ∧ False) ∧ (p3 ∧ ((p4 ∨ (p2 → False)) ∨ (((p4 ∨ ((((True → p2) → False) → p4) ∨ False)) ∨ (False ∧ p1)) ∧ p2)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198199866362500136039772445474 : (((p2 → p3) → ((p5 → p4) → (p4 ∧ True))) ∨ (((p2 ∨ p2) ∨ (p2 ∨ (p5 ∨ p2))) ∨ ((((True → p1) ∨ (p5 ∧ False)) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198278202441465877658371061929 : ((False ∧ (p2 ∧ ((p3 ∨ (p3 ∧ p3)) ∨ False))) ∨ (((p3 ∨ (((p1 ∧ ((False ∨ (p2 ∨ False)) ∧ p3)) ∨ p2) ∧ p1)) ∨ (p1 → p1)) ∨ p2)) := by
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
theorem thm_5_vars_116141380501227589175208009063 : (((p5 ∧ (p4 ∧ False)) ∧ (((((p5 → ((True → True) → (p3 ∨ False))) ∨ (p2 ∧ (p2 → p3))) ∨ p3) → (p4 ∧ p1)) ∨ p3)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654862386469996805863292455562 : ((((((p3 ∨ ((p1 ∨ (((p5 → (False → (p2 → (p5 ∧ True)))) ∧ p2) ∧ p3)) → p4)) → ((p4 → False) ∧ p2)) → p3) ∨ (True ∨ p4)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_78261249179540634259628821493 : (((p4 → ((((True → (p2 → (p2 ∨ (p3 → p5)))) ∧ (p4 ∧ p2)) ∨ ((p1 ∨ ((p1 ∨ p3) ∨ (p1 → p2))) ∨ p3)) ∨ p4)) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((((True → (p2 → (p2 ∨ (p3 → p5)))) ∧ (p4 ∧ p2)) ∨ ((p1 ∨ ((p1 ∨ p3) ∨ (p1 → p2))) ∨ p3)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49213234683427529287362719393 : ((((p3 ∧ p2) ∧ (((p1 ∨ p3) → (((p5 → p2) → (p3 ∨ p1)) ∧ (p2 ∧ (p3 ∧ p4)))) → (p4 ∨ p3))) ∨ (True ∨ (p4 ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923628285640806020794082083625 : (((((True → (True → (p2 ∧ p5))) ∧ ((False → p3) → (p2 ∧ False))) ∧ ((((p2 → ((p5 ∨ p3) ∧ p3)) ∧ p4) ∨ p5) ∨ (False → p3))) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h18 := h4 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726705025663905345523860641212 : (((((p4 ∧ p2) → False) ∨ (p3 → (((False ∧ (False ∨ (p4 ∨ (((p5 → (True ∨ False)) ∨ p3) ∨ (True ∧ p4))))) ∨ (p5 ∨ p3)) ∨ p1))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214999312810065102794596577769 : (((True ∨ False) → (p3 → False)) ∨ (p4 → (((p1 → p4) → (((p4 → p1) ∧ ((True ∧ ((True ∧ p4) ∨ p2)) → True)) ∧ (p3 ∧ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57923678360610459669934624024 : (((True → (False ∧ False)) → (((p3 ∨ (p1 → (p2 ∨ p4))) → (p5 ∧ (p2 ∨ (p2 ∨ p1)))) ∨ ((p2 ∨ (p2 → True)) ∨ (True ∧ p5)))) ∨ p5) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697863878875029370743881648356 : ((((((p5 → ((((False ∧ True) ∨ p1) ∨ p3) → False)) ∨ p5) ∧ False) ∨ (((p3 ∧ False) → p2) ∧ ((True → p4) ∨ ((False ∨ p1) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759369065576607777891384007111 : (((p2 ∧ (((p3 → ((p3 ∨ (False → (p2 ∧ ((False → (p1 → p2)) ∧ p2)))) → p2)) ∧ ((p5 ∨ False) ∧ True)) ∨ (True → (False → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20901039039518990972119356346 : ((((p1 ∨ p3) → (p4 ∨ (p2 ∧ (((False ∨ p2) ∨ p2) ∨ p3)))) ∨ (((((p1 ∨ p2) ∨ p2) ∨ (p5 ∧ False)) ∧ p3) ∨ (True ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_665215524283952702321021384946 : ((((((p4 ∧ (p1 → ((((p2 → (p4 ∧ p4)) ∨ p3) ∨ ((False → p1) ∨ True)) → (True ∨ p3)))) → False) ∧ p1) ∧ ((True → p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52283153123439013673293949588 : (((p4 → (((p5 ∨ (False ∧ p2)) ∧ ((True ∨ (False ∧ p5)) ∧ (p5 ∧ False))) ∧ True)) → ((p5 ∨ (((p5 ∧ False) ∧ p5) ∧ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172293823437503738124529937162 : ((((((p5 ∨ p4) ∧ (True → p3)) → p3) ∨ False) → ((p2 → p5) ∨ (True ∧ False))) ∨ (p4 → (True ∨ (False ∧ ((p1 ∧ p3) ∨ (True ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739189795797438252735681449607 : ((((p4 ∧ False) ∨ ((p2 ∨ (p4 → ((False ∧ False) ∨ True))) ∨ ((p3 → p2) → (((p1 ∨ p3) ∧ (True ∨ (p3 ∨ p2))) ∨ (True ∧ True))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184470265781780954158320368478 : ((((p4 ∧ (p4 ∧ (p1 → (True ∧ True)))) ∧ p4) ∨ (p2 ∨ p4)) ∨ ((False → p3) ∨ (p5 → (True ∧ ((p2 ∧ (p5 → True)) → (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682549358057857107410273290337 : (((((p2 → ((((False → (p3 → p2)) → False) ∨ p4) → False)) ∨ ((p5 ∨ p5) ∧ (p5 ∨ p2))) ∧ ((True → (True → p5)) ∧ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738706990051406698486507355985 : ((((p2 ∧ p2) ∨ ((((p3 ∧ (p5 ∧ p5)) → (((p3 → ((p1 → (p2 → p1)) ∨ p2)) ∧ (p3 ∨ p4)) ∧ True)) → False) ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620766602706239989057035813661 : (((((p4 ∧ p4) → (((((p1 → ((False ∧ (p4 ∧ (p3 ∨ (p1 ∧ p2)))) ∧ (True ∨ p2))) → (p1 ∧ True)) → False) ∨ False) ∨ p4)) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134234825279066313739136335325 : ((((p1 → ((p5 → p3) ∧ p1)) ∧ ((p5 ∨ ((p1 → (p2 ∧ p4)) → p3)) → (False ∨ (p2 → (p3 ∨ p4))))) ∨ p5) ∨ ((p4 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355867298037894354769948856488 : (p5 → ((((True ∧ p5) ∧ p5) ∧ ((((((False ∨ p1) → True) ∧ (p1 ∨ p4)) ∨ (p2 → False)) ∧ p3) ∨ (p2 ∨ True))) ∨ (p1 → (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221957458320152452402810408207 : (((True ∨ p2) → True) ∧ (p5 → (((((p1 ∨ (False ∨ (p1 ∧ p1))) ∨ p2) ∨ (p3 → True)) ∧ (p1 ∧ ((p1 → (p2 → False)) → True))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217313788529058430185229289395 : (((True ∨ (p4 ∧ p3)) ∨ False) → (p3 → (p5 ∨ (p2 ∨ ((p4 ∧ p3) → (((p5 ∨ (True ∨ (p5 ∨ (p2 ∨ p5)))) ∧ p3) ∨ (p1 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h7
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678217187352415538889567088408 : (((((((p3 ∧ (p5 → False)) → True) ∧ (p5 → (p3 ∧ p4))) ∨ ((True → True) → ((p5 → p2) ∧ True))) ∨ ((p1 ∧ p5) ∧ (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687651814025873819124689309651 : (((((p4 ∧ (p5 → (((((p2 ∨ True) ∧ (p5 ∨ False)) ∨ p4) ∧ p2) → p2))) → p5) ∧ ((True → (True ∨ (p5 → p2))) ∨ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762355388059066902160866658013 : (((p3 ∧ (((True ∨ (p2 ∨ False)) → (((True ∧ True) ∧ p4) ∨ (True → ((p3 ∧ True) → ((True → p4) ∧ p2))))) ∨ ((p2 → p1) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213333666695773529960443462751 : (((p2 ∧ (p1 ∧ p5)) ∧ False) ∨ ((p1 ∧ False) ∨ ((True → (False → ((((p1 ∨ p5) ∧ p5) ∧ p3) → ((True ∧ p1) ∨ (p5 ∨ True))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700949502757345923388521305826 : ((((((True ∨ p3) ∨ (False ∧ ((False ∧ p3) ∨ True))) ∨ p5) ∧ ((False → p3) → ((p3 → (False ∨ (p3 ∧ p4))) ∧ (p4 → (True → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187607002624029997133129813137 : ((p4 ∨ (((p5 ∧ (p5 ∨ p1)) ∨ p2) ∨ (p1 ∨ (p4 → p1)))) → (p3 ∨ (((p5 → (p3 ∧ (p3 ∨ ((p2 ∧ False) ∨ p4)))) ∨ p2) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
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
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43778822859438483975294327446 : ((((False ∨ ((p2 ∧ p1) → ((False ∧ True) ∨ (False ∨ (p4 ∨ (((p3 → (((p2 ∨ p2) → p3) → False)) ∧ p2) ∨ True)))))) → False) → p5) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p2 ∧ p1) → ((False ∧ True) ∨ (False ∨ (p4 ∨ (((p3 → (((p2 ∨ p2) → p3) → False)) ∧ p2) ∨ True)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149665741852014585045908832377 : ((p4 ∧ (p3 ∨ (((p1 ∧ (p1 ∨ p5)) → (p1 → p1)) → ((p4 ∧ ((p4 → p2) → p4)) → (p4 → p3))))) ∨ (True ∨ (p3 → (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165742985210809542500397054677 : ((((False → (p5 ∧ p5)) → p1) ∨ ((p5 ∨ ((True ∧ p5) ∧ (p4 ∧ (p1 ∨ False)))) ∨ True)) ∨ (((False ∨ (p4 ∧ p3)) → (False ∧ p2)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219074360894824502963664456240 : ((p5 ∧ (True → (False ∧ p2))) → (((((p1 ∧ (((p2 → p4) ∨ p4) → p2)) ∧ (p1 ∧ p1)) ∨ (p5 → (p4 ∧ p1))) ∧ (False ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58313052500766236315284349926 : (((True ∨ p5) ∧ ((p5 ∨ (True ∧ p5)) → (((((p3 ∧ True) ∨ p4) ∨ p4) ∧ (p3 ∨ False)) → ((p5 → p3) ∧ (p1 → (False ∨ p1)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29
  -- Implications on the right can always be decomposed.
  intro h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h2.left
  let h32 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h39 =>
          -- Conjunctions on the left can always be decomposed.
          let h40 := h39.left
          let h41 := h39.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
      case inr h49 =>
        -- False on the left can always be used.
        apply False.elim h49
  case inr h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h52 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h53.left
        let h55 := h53.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h56 =>
      -- False on the left can always be used.
      apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148214552299018459027249097536 : (((p3 → (((True ∧ (p4 → p1)) ∨ p3) → (((p2 ∧ p5) ∨ (True ∨ p2)) ∧ p3))) ∧ (False ∨ (p4 → p4))) ∨ ((p4 ∨ (p2 → p1)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53304577412844603584438760130 : (((p4 ∨ (p4 ∨ ((True → ((p5 → (p3 → p3)) ∧ p3)) → p3))) ∨ ((p1 ∧ ((p5 → p1) ∧ p2)) → ((p4 ∨ (p4 ∨ p4)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172884297742014895275479284961 : ((p1 ∧ ((True → p5) ∨ ((((True ∧ (p3 ∨ p4)) → p5) ∧ False) ∨ (False ∨ True)))) ∨ ((p3 → ((False ∨ p5) → False)) ∨ (True ∧ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246055160395508844150080542210 : ((p4 ∧ False) ∨ (p1 ∨ (p3 ∨ ((p1 → (((True → p4) → ((p3 ∧ True) ∨ (p2 → (p2 ∧ p1)))) ∧ (False → p1))) ∧ (True ∧ (False → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151082751733389129747014665330 : ((((p5 ∧ (((p3 ∨ p4) ∨ (False → p4)) ∨ ((((p1 → False) ∧ (p5 ∨ p4)) ∧ p1) → p5))) ∨ True) → p1) → ((False ∨ (True → False)) → p5)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803248639445698453464413433988 : (((p3 → (((((True ∧ ((p3 ∨ (p1 ∧ p1)) ∧ (p3 ∧ (p2 ∧ True)))) → ((False ∧ True) ∨ (p1 → True))) → p5) ∨ (True ∨ False)) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40885299925492642495555065148 : (((((p2 ∧ (False ∨ ((((p4 ∨ p4) ∧ p5) ∨ p3) → p2))) ∧ (p5 ∧ ((p4 → False) ∨ ((True ∨ p2) ∨ p5)))) ∧ (p5 ∧ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320395482664601071086620842368 : (p4 ∨ ((p2 ∧ True) → (p3 → (p2 ∧ (((p5 ∨ (p5 ∧ p4)) ∨ p5) → ((False ∨ False) ∨ ((p4 ∨ (p5 ∧ (p5 ∨ (False → False)))) ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47884581373734167174529481029 : ((((((((False ∨ (True ∨ p2)) → p5) ∨ (p3 ∨ ((p2 ∧ p1) → False))) ∧ (p4 ∨ (p3 → True))) → False) ∨ (p5 → False)) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49251843630370826123612336365 : (((True ∧ ((p1 ∧ (p2 → p2)) → (p5 ∧ (((p2 ∨ (p5 ∨ p3)) ∧ (p1 → p2)) ∧ (False → (True ∧ False)))))) ∨ (False → (p2 ∧ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_325026898162434289951271220862 : (p5 ∨ ((p3 ∧ p3) → ((p4 ∨ ((p2 ∧ (p4 ∧ False)) ∧ ((p3 ∧ (p2 ∨ ((p5 ∨ p4) ∨ (True ∨ False)))) ∨ p4))) ∨ (p1 → (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56432978500091946963061206341 : ((((p2 → True) ∧ (p5 ∧ p4)) → (((((p1 ∨ True) ∧ (False ∨ True)) ∨ ((p1 → False) ∨ True)) ∨ True) ∧ ((False → (False ∨ False)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137078712505578057653674555840 : (((p5 → p3) → (((p3 ∨ (p5 ∧ p1)) → p4) → (p3 ∨ (p4 → ((((p3 → False) → True) → (p3 → p5)) ∨ p4))))) ∨ ((p4 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865222372606094355695507418341 : ((((((True → (False ∧ True)) ∧ (False → True)) → ((((((p1 ∧ (False → p5)) ∨ p1) ∨ (True → p1)) ∧ False) ∨ (p1 → True)) ∧ p4)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → (False ∧ True)) ∧ (False → True)) → ((((((p1 ∧ (False → p5)) ∨ p1) ∨ (True → p1)) ∧ False) ∨ (p1 → True)) ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149645017124766814260755359156 : ((p4 ∧ ((p3 ∨ ((p2 → (p2 ∨ p4)) → ((False ∨ p5) → (p4 ∨ p5)))) ∧ (((True → p3) ∧ p3) → p2))) ∨ (((p2 ∨ True) ∨ p2) ∨ p4)) := by
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
theorem thm_5_vars_730193113100071264601206283314 : (((((False → True) → p4) → (((False ∨ p3) → (p5 ∨ ((((p3 → (p4 → p3)) ∧ p4) ∧ (((p4 ∧ p1) ∨ False) ∨ p1)) → False))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191832860076360091072979741645 : ((p3 ∨ (((p4 → p4) → (p2 → (p1 → p3))) → p4)) ∨ (p3 ∨ ((False → (False ∧ (False ∨ (p4 ∧ (p4 → True))))) ∨ (p5 → (False ∧ True))))) := by
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
theorem thm_5_vars_683808904772013495914879962515 : ((((((((p4 → p3) → (p5 ∧ (p5 ∧ False))) ∨ p1) ∧ ((p1 → p3) ∨ (p5 ∧ p2))) ∨ p1) ∨ (p2 → (p2 ∧ (p3 → (p4 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246273875313408548584818393253 : ((p4 ∧ p4) ∨ ((p2 ∧ (((p5 ∧ p3) → (p1 ∨ ((((p1 ∧ False) → True) ∨ p5) ∨ p5))) ∨ p3)) → (((True ∧ p3) ∨ p4) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_595548239895036460820320150478 : (((((p3 → (p4 ∧ (((p4 ∨ (p1 ∧ p4)) → p4) ∨ (p3 → True)))) ∨ ((p5 ∧ p5) ∨ (p5 ∧ ((False ∧ p4) ∧ (p5 ∨ p3))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193059268064775076159291096040 : (((((False ∧ p3) → p5) ∧ True) ∧ ((p4 → p1) ∨ p5)) → ((p1 ∨ True) ∧ (False → (p2 → ((((p4 → (p2 ∨ p4)) → p5) ∨ p1) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218659952291143670677476236774 : ((True ∧ (p1 ∧ (p3 → True))) → (p2 → ((p3 ∧ (p5 ∧ ((p4 ∨ p3) ∧ (p3 → p4)))) ∨ ((p4 ∧ (p5 → True)) ∨ ((p4 ∨ p3) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354695692028102229146675403463 : (p5 → (((p5 ∧ (True ∧ (p1 ∧ (((p4 ∧ (p5 ∨ False)) ∨ ((p5 ∧ (((False ∨ True) ∧ p3) → p3)) → p4)) ∧ p3)))) ∨ (False → p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266244430481416123380302656598 : (True ∧ (p5 → ((p2 ∨ (False ∨ (False ∨ ((((True → (p5 ∨ False)) ∧ p5) → (p2 ∧ True)) ∧ ((False ∧ (p3 ∧ (p2 ∧ p2))) ∨ p3))))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264008818665974194782714117650 : (True ∧ (((((p3 ∨ ((False ∧ p3) → p2)) ∨ p5) ∨ False) → (p3 ∨ p1)) → (p1 ∨ (((((True ∨ p3) ∧ p3) ∧ p4) → p2) → (True ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ ((False ∧ p3) → p2)) ∨ p5) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157686906159305940077219554274 : (((p3 ∨ (True → (p2 ∨ ((p1 ∨ (p4 ∧ False)) → (p2 → (p1 → p4)))))) ∨ ((p2 ∧ p3) ∧ p2)) ∨ (((True → p3) ∨ p2) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171662200857771054987656652233 : (((p3 ∧ ((False ∨ (p1 → ((p5 ∧ ((p5 → p4) ∨ True)) → p3))) → False)) ∨ p2) ∨ (p4 ∨ ((p2 ∨ (False → p2)) ∨ (True ∨ (False ∧ p2))))) := by
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
theorem thm_5_vars_976647812868756811395358619370 : (((True ∧ ((p4 ∨ ((((((p2 ∧ p5) ∧ p4) ∨ (True ∧ p3)) → ((True → p5) ∧ p3)) → p4) ∨ (((p2 ∧ p5) → False) ∨ True))) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ ((((((p2 ∧ p5) ∧ p4) ∨ (True ∧ p3)) → ((True → p5) ∧ p3)) → p4) ∨ (((p2 ∧ p5) → False) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611748157622238100224142791626 : (((((False → (((((p5 ∨ (p2 ∨ True)) → (p5 ∨ (p3 → p5))) ∧ (p2 ∧ p2)) ∨ (p5 ∧ ((False ∨ p4) ∧ True))) ∧ True)) → p5) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_233499424427478129546950146648 : ((p1 ∨ (p3 ∧ p4)) → ((((p3 ∧ ((True ∧ (p4 ∧ p4)) → (False ∨ ((p5 ∧ (False ∨ p4)) ∧ p5)))) ∨ p5) ∨ ((p1 → p1) ∧ True)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233557730099974697912955249843 : ((p1 ∨ (False → True)) → ((True → False) → ((((True ∧ (True ∨ p1)) ∨ (p3 ∧ (p5 ∧ (False ∧ p3)))) → (p2 ∨ ((p3 → p4) ∧ p1))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h20 := h2 h19
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h28 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h30 := h2 h29
    -- False on the left can always be used.
    apply False.elim h30
  case inr h31 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h33 := h2 h32
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303188323884762648828353873554 : (False ∨ (p4 → ((p3 ∨ (((p5 ∧ ((False ∧ p5) ∧ p2)) ∨ p4) ∨ p4)) ∧ ((False ∨ p5) → ((p2 ∧ p1) ∨ (((True ∧ p4) → p3) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54229257361324129578180374093 : (((((p4 → p1) ∨ (p4 ∨ (p1 ∨ p4))) → p5) ∧ (((((p2 ∨ ((p4 ∧ p1) ∧ p4)) ∨ (p2 ∧ True)) ∧ True) ∧ p5) ∧ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245082780719420241678113751435 : ((p1 ∧ p5) ∨ (False ∨ (p5 → ((((False ∧ p2) ∨ p2) → False) → (((((p2 → True) ∧ (p1 ∨ True)) ∧ (p5 ∨ p4)) → (p5 ∧ False)) → p3))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → True) ∧ (p1 ∨ True)) ∧ (p5 ∨ p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337768911217018474755224986876 : (p1 → ((((p4 → p1) ∧ ((p3 → p3) → p3)) ∧ (((p1 → p5) ∧ False) ∨ (p1 ∧ True))) ∨ ((((p4 → p1) ∧ (p3 → False)) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209194754141591015350366096238 : ((p4 ∨ ((p3 ∧ False) ∧ (True → True))) → (((p1 → p1) ∧ p5) → ((((p3 ∨ p4) → False) ∧ (p4 → ((p2 → True) → True))) → (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230070570458889855311884270335 : (((p2 ∧ p2) ∧ p5) → ((p4 ∨ p4) ∨ ((((((p4 ∨ True) ∧ p1) ∨ (p5 ∧ (p3 ∧ True))) ∨ ((p1 ∨ p1) → p5)) ∨ True) ∧ (False ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168904532932516995513138945299 : ((p5 ∨ ((((((p1 → False) ∨ p5) ∧ p4) → p1) ∧ p5) ∧ ((p3 → (p5 ∨ p4)) ∧ p2))) → (((True ∨ (p4 → (False ∨ False))) → False) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233737210551289316706720903446 : ((p3 ∨ (p4 ∧ True)) → ((((False → ((p4 ∧ False) → p5)) ∨ ((p3 → False) → p2)) → (((p2 ∨ p3) ∨ (p4 ∨ p1)) ∨ (p1 ∨ p4))) ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186918685686343807877093159759 : ((((p5 ∨ False) → p1) ∧ ((True ∧ False) ∨ ((p2 ∧ p5) ∨ p4))) → ((p4 → p1) → (((((p3 → True) ∧ (p1 → p3)) ∨ True) ∨ True) ∨ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607570680250170379472028372444 : (((((p1 ∧ (((p4 ∨ p5) → p3) ∧ ((p1 ∧ (p1 ∨ (p4 ∨ (p5 → ((False → p5) ∨ False))))) → (p4 ∧ (p2 ∨ False))))) ∧ p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803366531232566431910916050033 : (((p3 → ((False ∧ (((p4 ∧ p1) ∨ (p5 → (p5 ∧ False))) ∧ (((p3 ∨ p5) ∧ p3) ∧ (((p3 ∨ True) → p2) ∨ (p2 ∨ p2))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158787700435627105625491747334 : ((p5 ∧ (((False ∨ p5) → (True ∨ (p3 → ((p4 ∨ (True → p4)) ∨ ((True ∧ p2) ∧ p1))))) → p3)) ∨ (True ∨ (False ∨ (p1 ∨ (p2 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691495526621919098536604271096 : (((((p1 ∨ p2) → ((p1 ∧ p4) ∨ (True ∨ ((p3 ∧ p4) → ((p2 → p3) → p1))))) → (((True ∨ ((p5 ∨ p5) → p5)) → p1) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165883118526077523690667911238 : ((((p2 ∨ p2) ∨ p4) → ((p5 ∨ ((p5 ∨ True) ∧ False)) → ((p2 ∧ p2) ∧ (p3 ∨ p4)))) ∨ (True ∨ (p3 ∧ ((True ∧ p4) → (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800215847817063080044894242256 : (((p2 → (((((((((p2 → p1) ∧ p5) → p2) → ((p3 ∨ p2) → p5)) ∧ (p2 ∨ False)) ∨ (p3 → (False ∧ p2))) ∨ False) ∨ p2) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694517745509452879826980807695 : ((((False ∧ ((((p3 ∨ (False → False)) → False) ∧ True) ∧ (p5 → (p1 → False)))) ∨ (((p2 → (False ∧ False)) ∧ (True → True)) ∧ (True → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614738708677424286631310067062 : (((((((p3 ∨ (((p5 ∧ True) ∧ p4) ∧ False)) → ((False ∧ p5) ∨ p2)) ∧ ((True → p1) ∧ p3)) ∨ (p3 ∧ ((False ∧ p2) ∧ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181643074072763090716238120223 : ((p3 → ((p1 ∨ (((True ∨ (p1 ∧ p3)) → p1) ∧ p4)) ∨ (p3 ∨ p5))) → ((((p1 → (p3 ∨ p1)) → p1) → p3) ∨ ((p5 → True) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307386751716908025729433708896 : (p1 ∨ (p4 ∨ ((p5 → ((((False → p4) → False) ∧ p3) ∧ (True ∨ p3))) ∨ (p2 ∨ (((((p4 ∧ p4) → False) ∨ p3) → True) ∨ (p2 ∧ p4)))))) := by
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
theorem thm_5_vars_68805415895825358101424275837 : ((p4 → (((p1 → False) ∧ (p2 ∧ p3)) ∨ (p4 ∧ (((p1 ∧ (p2 → ((p5 ∧ (True ∧ p3)) → False))) ∨ (True ∨ (True ∧ p5))) ∨ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49074611895593849764515808159 : ((((((((True ∨ (p2 → p2)) → p1) ∨ p2) ∨ (p3 ∨ ((p5 ∨ (p1 ∨ p5)) → p3))) → p3) → (p3 ∧ True)) ∨ (True ∨ (p2 ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47412626768942475112790891504 : (((False ∧ ((p5 → (False ∨ True)) ∧ ((p3 → False) ∧ ((p3 ∨ True) ∧ (p4 → ((p4 → (False → False)) → (p1 ∧ p1))))))) ∨ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736308480351813987722907992455 : ((((False → p4) ∧ ((True ∧ (((((True ∨ p1) → p4) → ((((p1 → p5) ∧ p3) ∨ (p1 → True)) ∨ p3)) ∨ p3) → False)) → (p2 ∧ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((True ∨ p1) → p4) → ((((p1 → p5) ∧ p3) ∨ (p1 → True)) ∨ p3)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((((True ∨ p1) → p4) → ((((p1 → p5) ∧ p3) ∨ (p1 → True)) ∨ p3)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h14 := h10 h11
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137256958754070904653591097684 : ((p1 ∧ ((p5 → p2) ∧ ((((((p2 ∨ p4) ∨ p4) ∨ ((p3 ∧ (p2 → p3)) ∨ p5)) ∨ (p5 ∨ p1)) ∧ False) ∨ p4))) ∨ ((True → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68475954221478700178277053261 : ((p3 → (p5 ∧ ((True ∧ (False ∧ (False ∨ p2))) ∨ ((True ∧ (((p1 → ((True ∨ p3) → ((False → p1) ∨ True))) ∧ p2) ∨ p4)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43954079425167395102915746576 : (((((p2 → False) ∨ (p5 ∨ (((p4 → ((((True ∧ p5) → p1) ∧ p4) → False)) → (p2 → p4)) ∧ (True → True)))) ∨ (False → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48987693689180745084519657681 : (((((p3 ∨ p4) ∧ ((((p2 ∧ False) ∧ (p5 ∨ (True ∧ p5))) ∧ (((p1 ∧ p4) → True) ∧ p1)) ∧ True)) ∨ p2) ∨ (p3 → (p3 ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643935978048147797214172263244 : ((((True ∨ (((p2 → p5) ∨ (False ∨ ((((p1 → False) ∧ (p5 → True)) ∨ (True → ((p2 ∨ p5) → (False ∧ p2)))) ∨ p4))) ∧ p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



