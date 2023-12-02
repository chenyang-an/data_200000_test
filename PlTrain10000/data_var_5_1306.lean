variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585621837834163814770452236304 : ((((((p3 ∨ ((p5 → (((p1 ∨ True) ∧ (True → (p2 ∨ p1))) ∧ (p1 ∧ False))) → (((p5 → True) → p2) ∨ p1))) ∨ True) ∧ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349142845407078661337940966373 : (p3 → (True → (p3 → (((True ∧ ((((p1 ∨ p1) ∨ ((True ∨ p3) → p4)) ∨ (p1 ∧ p1)) ∧ p1)) ∨ (p5 ∧ (p5 ∧ (p5 → True)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264176308428224850218408516704 : (True ∧ ((p2 ∨ (((p2 ∨ (p2 ∧ True)) ∨ p4) ∧ True)) ∨ (((p3 → (((True ∧ True) ∨ p2) ∨ p1)) → (p4 ∧ True)) ∨ (True ∨ (p5 ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147161546539317515784432605605 : (((p5 ∧ ((p5 ∨ (((False ∧ p5) → p3) ∨ (((p4 → (p2 ∨ p5)) ∧ True) ∧ (p2 ∧ True)))) ∧ p2)) ∧ p2) ∨ (p5 → (p5 → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206964887061100416769465125402 : ((((p5 ∧ (p3 → False)) → p2) ∧ p1) → ((((p5 ∧ True) ∧ ((p5 → (False → True)) → False)) ∨ (p2 ∨ (p2 ∨ True))) ∨ (p4 ∨ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_655398689529182774108135100262 : ((((((((p5 ∨ p1) ∨ (p4 ∧ (False ∨ ((p3 → p2) ∨ p5)))) ∨ False) ∧ (p4 → (p4 ∨ (p2 ∧ p5)))) ∨ (True → False)) ∨ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241326807384232690792485743824 : ((False → True) ∧ (p5 → (((((p3 → p1) ∧ p3) → True) ∧ (p1 → True)) → (p2 → ((((True → p2) ∨ (True → (True → p4))) ∧ p1) ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797183161036276560969225806297 : (((p1 → ((p5 ∨ ((False ∨ ((p4 ∧ (p3 → ((p2 ∨ (p1 ∨ p5)) ∧ (p2 ∧ p4)))) → p2)) ∧ (p1 ∨ ((p4 ∨ p2) → p1)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314958510358648694074661941265 : (p3 ∨ (((p5 ∨ p1) ∧ ((p4 → p4) ∨ ((p5 → p2) ∧ p4))) → (p3 → ((p2 ∨ (p2 → ((p5 ∨ p2) ∧ p3))) ∨ ((True ∨ p4) ∨ False))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351233260748490456328787592860 : (p4 → ((((p4 → ((p1 ∧ p1) ∧ ((True ∧ p5) ∧ (False ∧ (False ∨ p3))))) ∨ p3) ∨ (p5 → (p3 ∨ (p5 ∧ p4)))) ∨ (p2 → (False ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42812170184979590687801055560 : (((p1 → (((((True ∧ p5) ∧ (p4 ∨ (p3 ∨ p1))) → p2) → ((p5 ∨ p3) → (p4 ∧ (p5 → (p4 → False))))) ∧ (p4 → p5))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62372900053013271847535873015 : ((p3 ∧ (((p2 ∨ (False ∨ p1)) ∧ ((p3 → (p4 ∨ p2)) ∨ ((p4 → p1) → (True ∧ False)))) → ((p3 ∨ p4) ∧ (p5 ∧ (p5 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42201329311462858503625100799 : (((True ∧ (p3 ∧ ((((True ∨ p5) ∧ (((p1 ∨ ((p5 ∨ (p3 → False)) → p1)) ∧ ((True ∨ True) ∨ p5)) ∨ p5)) ∨ False) ∨ p3))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162006441358658869291451945908 : ((p3 → (p3 ∨ (p5 → ((p5 ∧ p4) → ((p2 → p2) ∨ ((p3 ∧ (p3 ∨ (p3 ∨ True))) ∨ False)))))) → ((p1 ∨ p3) → ((p3 → p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443598268830585806869818092703 : ((((((p4 ∨ (False ∨ p3)) → (True ∧ p3)) ∨ (p2 ∨ (False ∨ ((((p1 ∧ p1) → (p4 ∨ p2)) → p4) ∨ True)))) ∨ ((p1 ∨ p2) ∨ p4)) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111073321346857168935314731325 : (((((True ∨ (p3 ∨ (p4 ∨ (p1 ∧ (p3 ∨ (p3 ∨ (True → p2))))))) ∨ False) → (((p3 ∨ p2) → p1) → (p4 ∨ p1))) ∧ True) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247479502051611178529847430839 : ((False ∨ p3) ∨ ((((p1 → (((p5 ∨ ((p2 ∧ p5) ∨ True)) ∨ True) ∧ (True ∨ (True → ((p5 ∨ p4) ∧ p5))))) ∨ p3) ∨ p2) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252144834107798139138152741578 : ((p4 → p3) ∨ ((((((p5 ∨ ((p2 → p5) ∧ (p3 → p2))) ∨ p1) → True) → ((p3 ∨ (p1 → False)) ∨ True)) ∨ ((p3 → p3) → p5)) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165595439694758787210209268752 : (((((p2 → p3) → (p3 ∨ (True ∨ p5))) ∨ p5) → (((p2 → p4) ∨ p4) ∨ (p1 ∧ True))) ∨ ((((False → p2) ∧ p3) → True) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353713170578964835013253618694 : (p4 → (True → (((((p2 → True) ∧ ((False → p2) ∧ ((p3 ∨ ((False ∧ p1) ∧ ((p3 ∧ False) ∧ (p5 ∨ p2)))) ∨ p4))) ∨ True) ∧ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_141166215304238007711825207282 : (((p4 ∨ (False → (p5 ∨ (True ∨ False)))) ∧ (((True → p3) → p1) ∧ ((p4 ∧ p1) ∧ (p4 ∧ (p3 ∧ (p3 ∨ True)))))) → (p2 → (True ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h22.left
    let h26 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428661864359781302553247908369 : (((((((p3 → (p3 ∨ p3)) → (((p4 → p5) ∨ ((((p1 → True) ∧ p3) ∨ p1) → p5)) → p2)) ∧ False) ∧ (True ∨ p4)) ∨ (False ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134245133773067855315531005988 : ((((p5 ∨ ((p3 ∧ p4) ∨ p3)) → (p4 ∧ (((True → p1) → p2) ∧ ((False → p4) ∨ ((p1 ∧ p1) ∧ p4))))) ∨ True) ∨ (True ∧ (p4 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15154320473838367896480900431 : (((p2 ∨ (p2 → (((p2 ∨ ((p1 ∨ p1) → (p3 ∧ p3))) ∨ p3) → (p5 → (p2 ∧ (((True → p4) ∨ True) ∨ False)))))) ∨ (p5 ∧ p3)) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668939621179932116345546977552 : (((((p2 ∨ ((((((False ∨ True) ∧ p2) ∨ p1) ∨ p4) → ((((p3 → p3) ∨ False) ∨ False) → False)) ∧ p2)) ∨ True) ∨ ((p3 ∧ p2) → False)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_303102763545972232058154446991 : (False ∨ (p3 → ((((p2 ∨ (((p5 ∨ p5) ∨ p5) → (p3 → p2))) → (p5 ∧ (p2 → (False ∨ ((p4 → (p3 ∧ p4)) ∧ p2))))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347874991444178476342556831814 : (p3 → ((p2 → (p2 → p5)) → (((((p4 → ((p5 ∨ p1) ∨ True)) ∨ (p1 ∨ p4)) → p4) → (p5 ∨ (p4 ∨ p4))) ∨ (p3 → (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → ((p5 ∨ p1) ∨ True)) ∨ (p1 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264083176569301477595464919064 : (True ∧ ((p4 ∨ ((True ∧ (p5 ∨ p1)) ∨ (p1 → (p2 ∨ False)))) ∨ (((p5 ∧ ((p1 ∧ False) → (p4 → True))) → False) → (False → (p3 ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148786374251402466557946438829 : (((p2 ∧ (p2 → ((False → True) → False))) ∨ (((p4 ∨ ((p5 → False) ∨ p1)) → p4) ∧ (p1 ∨ (p2 → p3)))) ∨ (((False ∨ False) ∧ p4) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695834763831797291868073267521 : (((((p4 ∧ p3) ∧ (((p4 ∧ (p2 → p2)) ∨ ((False ∨ True) ∧ p4)) → True)) → (p3 → ((False ∧ (False ∨ ((False ∨ p5) ∧ True))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241354124093580629835146406079 : ((False → False) ∧ ((((((p5 ∨ True) ∧ True) ∧ p1) ∨ p3) ∨ (((p3 ∨ p2) → (True ∧ p5)) ∨ False)) ∨ (False → ((p3 → (p2 → p2)) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207890263326517855961654127099 : ((((p1 → False) → True) ∧ (p3 → p1)) → (((True ∨ p5) ∧ p3) → ((p1 ∧ (p3 ∧ ((p5 ∨ (p5 → ((True ∨ p5) ∨ False))) → p2))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639420868094181913666225465859 : (((((p5 ∨ ((p2 ∨ p5) ∧ p3)) → ((p4 ∧ (p2 ∧ (((p2 ∧ ((p5 ∨ True) ∨ (p5 ∧ p1))) ∨ False) → p1))) ∧ (p2 ∨ p1))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601082455763268258066132811469 : ((((p1 ∧ (False ∧ ((p4 ∨ (((p5 ∧ p5) ∨ ((p1 ∨ (((p2 ∨ ((p1 → True) ∨ True)) ∧ False) ∨ p4)) ∧ p2)) → True)) ∧ p5))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78724138804684408590327095369 : ((((True → (True ∧ (False ∧ ((((p5 → p1) → True) → False) → p2)))) ∧ (((p3 ∧ ((p2 ∧ p1) → p3)) → False) → True)) ∧ (p2 → p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773341794977211528091562282814 : (((False ∨ ((p2 ∧ (p5 ∧ ((((((p1 ∨ True) → (True ∧ (p1 ∨ (p3 ∧ p4)))) ∨ p1) ∨ (p3 ∧ p3)) ∧ True) → (p2 ∧ p3)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172639775136661250089503855569 : (((False ∨ True) ∧ (p2 ∧ ((p4 ∨ ((p5 ∧ p1) → ((p2 → p4) → True))) → False))) ∨ (((p3 ∧ False) → (False ∨ ((p1 → p2) ∨ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231898830912629500314358319740 : (((False ∨ True) → True) → (((p3 → p1) ∧ p5) ∨ ((p3 ∧ ((p4 ∧ (p3 → ((p1 ∧ p4) ∧ p5))) ∧ ((p4 → (p1 ∨ p3)) ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351243205872946067726218573614 : (p4 → (((False ∧ (p5 ∧ (p2 ∨ p1))) ∨ (((p3 ∧ (p1 ∨ (p3 ∨ p5))) ∧ (p2 ∧ (p3 ∨ True))) ∧ (True ∧ True))) ∨ ((p3 → p3) ∨ p3))) := by
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
theorem thm_5_vars_57186404572355988685884810577 : ((((p1 ∨ p2) ∨ p1) ∨ (p2 ∨ ((((((p2 ∧ ((p3 → (p5 → p3)) ∨ (p1 ∨ (p2 ∧ True)))) ∧ False) → p5) → True) → False) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42489411645923009146949562314 : (((False ∨ (((((((p5 ∧ ((p5 ∨ (p2 → p1)) ∧ p1)) ∧ p2) ∨ ((p5 → p5) ∧ False)) ∨ (p3 ∧ p2)) ∧ p2) ∧ True) ∨ True)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799115865965803578477371953321 : (((p1 → (True ∧ (p4 ∧ (((p2 ∧ ((p1 ∨ (p1 ∧ False)) ∧ p1)) ∨ p3) ∨ ((((p5 ∨ ((True ∨ True) ∧ p4)) → True) → p4) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754223315406469547396828072828 : (((False ∧ ((False ∧ p4) ∧ ((((((((False ∧ False) ∧ p2) ∧ True) ∨ p2) ∧ (((p4 → p4) → p3) ∧ p3)) ∨ p1) ∨ False) ∧ (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54194414534430007378425428383 : (((((p1 ∨ ((p2 ∨ p4) ∨ True)) ∨ p5) ∨ False) ∧ (p3 ∧ ((True ∧ p2) → (p3 ∨ ((((p1 → (True ∨ p1)) ∧ p5) ∨ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260800960942024361503164516808 : ((p3 → p5) → ((False → False) ∧ ((p5 ∨ ((p2 ∨ (p3 ∨ ((p4 ∧ p2) → p2))) → p2)) ∨ (((p2 ∨ ((True → True) ∨ p3)) → True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240893389676980206872800922448 : ((True → True) ∧ (p2 ∨ ((p5 → (((((p4 ∨ (p3 ∨ p5)) ∨ p1) → (p5 ∧ False)) ∨ False) ∨ (True ∨ (p1 ∧ ((True → True) ∧ False))))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476167024814630716502382459432 : (((((((p1 ∧ (p4 ∨ p3)) ∧ p2) ∨ p5) ∨ (p3 → p3)) ∨ ((((p1 → p4) ∧ (((p2 ∧ p3) ∨ (False ∨ True)) → p1)) ∨ p5) → p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134433336134097344723700127015 : (((p5 → ((p3 ∨ (p1 ∨ p2)) ∨ ((p4 → ((((p4 ∨ p4) ∨ p4) → p3) ∨ (p1 ∨ (p3 → p5)))) ∨ p1))) ∨ p4) ∨ (False ∨ (p5 ∧ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303981022007117531953475820809 : (p1 ∨ (((p4 ∧ p2) ∧ ((p4 ∨ p1) → ((((p2 ∧ p1) ∨ ((False ∨ p3) ∧ (((p3 ∧ p5) ∨ True) ∧ False))) ∧ True) ∧ (p1 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164860249413119596222912080159 : (((p2 ∨ ((p2 ∨ (p2 → ((p4 → p4) ∧ ((True ∧ p3) ∨ (False ∨ p4))))) ∧ False)) ∨ True) ∨ (((p5 → p4) ∧ p3) ∧ (p3 ∨ (True → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147976360771567239430244359433 : (((((((((False ∧ p2) ∧ False) ∧ (False ∧ False)) ∨ ((p1 → True) → p4)) ∧ p3) ∨ p5) ∧ p5) ∨ (p3 ∧ p2)) ∨ (p1 → (True ∨ (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319638312675628649070983109360 : (p4 ∨ ((((p4 ∨ (False ∧ p5)) ∧ p1) ∨ (p1 → False)) ∨ (p5 ∨ ((((p1 → ((False ∨ False) ∨ p5)) ∨ (False → p1)) → False) → (p2 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → ((False ∨ False) ∨ p5)) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → ((False ∨ False) ∨ p5)) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234474910381564177631454951992 : ((p2 → (p2 ∨ False)) → (((((p1 → (((p5 → False) → p4) ∧ p3)) ∧ True) → p3) ∨ p1) ∨ ((((False ∨ True) ∨ (p3 ∨ p4)) ∨ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49929816572198646244881266596 : ((((False ∨ ((p5 → p3) ∨ ((p4 ∨ (p1 ∧ p3)) ∨ (((True → p2) → (p3 ∧ p1)) → p3)))) → False) ∧ ((p5 ∨ False) ∧ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165528766174163712913629727155 : (((p5 ∧ ((p4 ∨ p5) ∨ (p1 ∨ (p4 ∨ (p2 ∧ p4))))) → (p4 → ((p4 → p1) ∧ False))) ∨ (False → ((((p1 ∨ p1) ∨ p1) → p3) ∧ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165066218497660337625213971441 : (((p2 ∧ ((False → (True ∧ (p3 ∨ (p4 → (p5 ∧ False))))) ∧ ((True ∧ p4) ∧ p2))) → False) ∨ ((False → (p2 ∧ ((p4 ∧ False) → p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4242109020925196932354988754 : (p5 ∨ ((True → False) → (p2 ∨ ((((True ∨ p2) ∧ p5) ∧ (True ∧ p2)) ∨ (((p4 ∨ False) → (p5 ∨ (p2 ∨ False))) ∨ (False ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352497504506074366547806910149 : (p4 → ((p2 → (p2 ∨ p4)) → (((p1 ∧ ((p4 → p1) ∧ p2)) ∨ (p3 ∨ False)) ∨ ((True ∨ p2) ∧ ((False ∨ (p2 ∧ (False ∧ p4))) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634905088504468598328389228127 : (((((True ∨ ((((p3 ∧ (p1 → (p2 ∨ ((p3 ∧ p2) ∧ p2)))) ∨ (p1 ∨ p2)) ∧ (p3 ∧ p5)) → False)) ∨ (True → (False ∨ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662687214764449650520936981972 : (((((((True ∨ p1) ∨ p4) → p2) ∨ (((p1 ∨ (p2 → ((p4 ∧ p2) → ((p4 → p5) → (p1 ∧ p3))))) ∨ p2) → False)) → (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630104941372618549017217862643 : ((((((p5 ∨ (p4 ∧ p3)) → ((((((True → (p2 ∧ p1)) ∨ False) ∨ True) ∧ p3) ∧ True) ∧ ((False ∧ (p5 ∨ p4)) ∧ p1))) ∨ p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89382282380097884372599468786 : (((p1 → (p2 ∧ False)) ∧ ((True ∨ (False → (False → (p4 ∨ (True ∧ (((p1 ∨ (True → (True ∨ False))) → p2) → (p3 → p5))))))) ∧ p1)) → False) := by
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
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167611909372384676652498170861 : (((((p2 → ((p2 ∨ p1) ∨ (True ∧ (p2 → (p2 ∧ p3))))) ∨ p1) ∧ False) → (p5 ∧ p1)) → (((False → p4) → p4) → (p4 ∨ (p5 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652480574839470717129459402355 : ((((p5 ∧ (p4 → (False ∧ (p5 → (False ∨ (True ∨ ((p2 ∧ False) ∨ ((p2 ∨ (p5 ∧ (False ∨ (p2 → p1)))) → p3)))))))) ∧ (p5 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257635236058952055672452009085 : ((p3 ∨ p2) → ((p4 ∨ (((True ∨ p5) ∧ (p1 ∨ p1)) ∨ True)) ∨ ((p3 ∧ p1) → ((((p1 → p3) ∨ p3) → True) → (p1 → (p4 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205298375508428673813364741882 : (((p5 ∧ (p4 ∧ False)) ∨ (True ∧ p3)) ∨ (((p1 ∨ ((True ∧ (p4 ∨ (p2 ∧ p5))) ∧ True)) ∨ (True → p3)) ∨ (p1 → (True ∨ (False ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257213795830752198901683628034 : ((p2 ∨ p2) → (((p2 → p3) ∨ (p5 ∨ True)) → ((p1 ∨ (p1 → False)) → (((((True → (p3 → p5)) ∨ p1) ∨ (p4 ∨ p4)) ∧ p3) → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h11 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h12 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h15 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h16 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h18 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h19 =>
              -- One of the premise coincides with the conclusion.
              exact h6
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h26 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h27 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h29 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h30 =>
              -- One of the premise coincides with the conclusion.
              exact h6
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h38 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h39 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h41 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h42 =>
              -- One of the premise coincides with the conclusion.
              exact h6
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h44 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h45 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h46 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h47 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h48 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h49 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h50 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h51 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h52 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h53 =>
              -- One of the premise coincides with the conclusion.
              exact h6
  case inr h54 =>
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h56 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h57 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h58 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h59 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h61 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h62 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h63 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h64 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h65 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h66 =>
              -- One of the premise coincides with the conclusion.
              exact h6
      case inr h67 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h68 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h69 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h70 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h71 =>
          -- Disjunctions on the left can always be decomposed.
          cases h71
          case inl h72 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h73 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h74 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h75 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h76 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h77 =>
              -- One of the premise coincides with the conclusion.
              exact h6
    case inr h78 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h79 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h80 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h81 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h82 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h83 =>
          -- Disjunctions on the left can always be decomposed.
          cases h83
          case inl h84 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h85 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h86 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h87 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h88 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h89 =>
              -- One of the premise coincides with the conclusion.
              exact h6
      case inr h90 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h91 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h92 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h93 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h94 =>
          -- Disjunctions on the left can always be decomposed.
          cases h94
          case inl h95 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h96 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h97 =>
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h98 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h99 =>
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h100 =>
              -- One of the premise coincides with the conclusion.
              exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117643785449573277142100181630 : ((p3 ∧ (((True ∧ (p2 ∧ (p1 ∧ (p5 → p1)))) → (True ∧ ((p2 → (((p2 → False) → p3) ∧ (p2 ∧ p3))) ∨ True))) → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263150560445002118163008876943 : (True ∧ ((True ∧ (((((p2 ∨ True) → (((p5 ∨ False) ∨ p2) ∨ True)) ∧ ((p1 → p3) → True)) ∨ (p4 ∨ p1)) ∨ (p2 → p2))) ∨ (p4 ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_147460089657845544479066669693 : ((((p2 → p3) → (p2 ∨ ((p4 → (p4 → (((p3 ∨ p1) ∧ ((p4 ∧ p2) ∨ p2)) → p4))) ∧ p3))) ∨ p3) ∨ (True ∨ ((p1 ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114677848829414943936904588961 : (((p4 ∧ (((p2 ∧ True) ∧ False) ∧ (True ∧ ((p2 ∨ ((p3 → True) ∧ True)) → p3)))) ∨ (((p1 → p2) → (p1 → p5)) ∧ False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191770829435898109964141191547 : ((p1 ∨ (((p2 ∨ (p5 ∨ p2)) ∨ p5) ∨ (p2 → p3))) ∨ (((((True → ((False ∧ (p1 ∨ p2)) ∨ (True → p3))) ∧ p5) → p3) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197084920038670386890912181717 : (((p1 ∧ (((p2 → True) ∧ False) → False)) ∨ p5) ∨ ((p1 ∨ (p5 ∧ (((p4 ∧ p2) ∨ p4) ∨ (((p4 ∨ False) ∧ p3) → p5)))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315246839953616439233860611910 : (p3 ∨ (((p1 ∨ False) ∧ (p4 ∧ True)) ∨ ((True → (p2 ∨ (((p5 ∧ (p5 ∨ p5)) → p5) ∧ (True ∨ ((True ∧ p2) → (p3 ∧ p4)))))) ∨ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219966675797652970916949486543 : ((p5 → ((p5 → p1) ∨ p5)) → (((p3 ∨ p5) → p5) ∨ ((p3 ∧ (p4 ∧ (p1 ∧ (p3 ∨ p4)))) → ((p4 → True) ∨ (p2 → (True → p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111928828594820545553316310036 : ((((((p5 ∧ (p5 ∨ p4)) ∨ p1) ∧ ((p1 ∨ p1) → p2)) ∧ ((p4 ∧ p4) → (p1 → ((True ∧ (p5 → True)) ∨ True)))) ∨ p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65378390021773301390869193333 : ((p3 ∨ (((p5 ∨ ((p4 ∨ (p1 ∨ p4)) ∨ p3)) ∨ p5) ∧ ((False → ((p4 ∧ ((False → (p1 ∨ True)) → False)) ∧ p3)) ∨ (p3 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355769840004060934803351238399 : (p5 → (((((((p3 ∧ (p1 → (p2 → p3))) → False) ∧ (False ∨ p1)) → ((True ∨ (False ∨ True)) ∨ p2)) → p2) ∨ p5) ∧ (p4 ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135556744800184230627658530075 : (((p3 ∧ ((((p2 → (True ∧ (True → False))) ∧ (p3 → (p1 ∧ p1))) ∨ p2) → False)) ∧ (True → ((p5 ∨ True) ∨ p2))) ∨ (True ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193740275722497720724072115651 : ((p3 ∧ (((p1 ∨ True) ∧ ((p5 ∨ p3) → p2)) ∧ p3)) → ((((p2 → p4) ∧ (p4 → True)) ∧ p4) ∨ (((p4 → False) → p2) ∨ (False ∨ p1)))) := by
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
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : (p5 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678768441211468692756267009218 : (((((p2 → False) → (p5 ∧ (((p5 ∨ (p4 ∨ (((True ∨ p1) ∨ p4) → p2))) → (True ∧ p4)) → False))) ∨ (p1 → ((False → p1) ∨ p1))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789879472505496854058098287655 : (((p5 ∨ ((p3 → (p4 ∧ p2)) ∨ (((False ∨ ((((True → True) → (False ∧ p4)) ∧ p2) ∨ (True → True))) ∨ p4) ∨ ((p4 ∧ p1) → p5)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_50677153408522880621009928725 : ((((p2 ∧ (p3 → (True → True))) ∧ ((False ∧ p1) → (p4 ∨ (p2 ∧ (((p3 → True) ∧ True) → p5))))) → (p1 ∨ ((p1 → False) ∨ p2))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135698137387216402574349292757 : (((((p4 ∨ p5) ∧ ((p1 → p4) ∨ p1)) ∧ (True → (p4 ∧ (p3 ∨ p5)))) ∧ (((p4 ∨ (False → p1)) → p2) ∨ p3)) ∨ (p4 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45468183573879251560555835 : (True ∧ (p5 → (((p5 → (((True ∨ (p5 → ((p5 ∧ True) ∧ p3))) → (p1 ∨ p1)) ∨ ((p2 → p5) ∨ p3))) ∧ p5) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313084604726903270846690273378 : (p3 ∨ (((((((False ∨ p4) → (p1 ∧ p1)) ∨ (True ∨ p5)) → False) ∧ (p4 → (p4 ∧ ((p5 ∧ (False ∧ p3)) → p1)))) ∨ (False → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117434911423300412169048668438 : ((p1 ∧ (((False ∧ False) → ((p3 → (p1 ∧ p2)) → (False ∨ (p5 ∨ p3)))) ∧ (((p3 ∧ p4) ∨ p5) ∨ (p5 → (p3 ∧ p3))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656502458962476593939600371194 : ((((((p1 → (p5 ∧ p5)) ∨ (((False ∨ p1) ∨ p3) ∨ p2)) → (p2 ∧ ((False → p5) ∧ (((p2 ∧ False) ∧ p2) ∨ p5)))) ∨ (p1 → p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_179146462811481582887378153112 : ((p2 ∧ ((((((p3 → p5) ∨ (True ∨ p2)) → p1) ∨ p5) → p3) ∧ False)) ∨ (p3 → (p2 → (((((False → p4) → p3) ∨ p3) ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356824757446651017961066765175 : (p5 → ((p2 ∨ ((p3 ∧ p4) → p5)) ∧ (False ∨ (p5 ∧ ((((p1 ∨ p3) ∧ p3) ∨ p5) ∨ ((((p3 → p4) → True) → p1) ∧ (p3 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790914369518420830927581906051 : (((p5 ∨ (p4 → ((((True ∧ (p3 ∧ ((p3 ∧ (True → p4)) → p1))) ∨ p4) ∨ (((False ∧ (p1 ∨ p2)) ∨ (True ∨ True)) ∨ False)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171511008322992007486313079209 : ((((((p2 ∧ (p3 ∨ p3)) ∧ (False ∧ p5)) ∧ ((p5 ∨ p3) ∧ p5)) ∧ p5) ∨ True) ∨ ((p5 → p1) → (((True → (p3 ∧ p1)) ∧ p5) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149469822657883299616372323997 : ((False ∧ ((True → False) ∨ (((p4 ∧ (((p4 → p2) ∧ p5) → ((p4 ∧ (p1 → p1)) ∧ p3))) ∨ p1) ∨ p4))) ∨ ((False → (p1 ∨ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301816873098502178143238635605 : (False ∨ ((False ∨ p4) ∨ ((p2 → ((p5 ∨ p2) ∧ (((False ∧ (True ∧ (True ∧ (p3 ∨ (p1 ∨ p4))))) → p4) ∧ p4))) ∨ ((p2 → True) ∨ p5)))) := by
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
theorem thm_5_vars_671426830655098812589976238327 : ((((p1 → ((True ∧ p3) → (((p5 → True) → (((False ∨ p5) ∨ ((p4 ∨ p1) ∨ p1)) ∧ (p2 ∧ p1))) → p5))) ∨ (False → (p1 ∧ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225253768198847455588665286947 : (((True ∨ False) ∧ p1) ∨ ((p1 ∨ (((False ∨ True) → (False → ((p5 ∧ p4) → (p4 → (p1 ∨ True))))) ∧ True)) → (p5 ∨ ((p1 ∨ p4) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49708863493121159589269806375 : ((((p2 → p3) → ((p2 ∧ (p1 ∧ p4)) ∧ ((False → ((((p5 ∨ p2) ∧ p4) → (True ∨ False)) ∨ p4)) ∧ p1))) → ((p1 ∨ True) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773217871357954610167901200019 : (((False ∨ (((((p2 ∧ p1) ∨ (p3 ∧ p2)) ∧ (p3 ∧ ((True ∧ p4) → (p5 → (((p2 → p2) → True) → p5))))) ∨ (p4 → p4)) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192935133850338056441595898206 : ((((p3 ∨ (p2 ∨ p4)) ∧ (p4 ∨ p1)) ∨ (True ∨ False)) → (((p5 ∧ p5) → (((True → False) ∧ True) → ((False ∧ True) ∧ (p4 → False)))) ∨ p2)) := by
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
      cases h4
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h7.left
        let h12 := h7.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h14 := h9 h13
        -- False on the left can always be used.
        apply False.elim h14
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h8.left
        let h17 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h7.left
        let h19 := h7.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h21 := h16 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h23.left
        let h28 := h23.right
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h30 := h25 h29
        -- False on the left can always be used.
        apply False.elim h30
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the left can always be decomposed.
        let h32 := h24.left
        let h33 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h34 := h23.left
        let h35 := h23.right
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h37 := h32 h36
        -- False on the left can always be used.
        apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h43 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h44
          -- Implications on the right can always be decomposed.
          intro h45
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- Conjunctions on the left can always be decomposed.
          let h48 := h44.left
          let h49 := h44.right
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h50 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h51 := h46 h50
          -- False on the left can always be used.
          apply False.elim h51
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h52
          -- Conjunctions on the left can always be decomposed.
          let h53 := h45.left
          let h54 := h45.right
          -- Conjunctions on the left can always be decomposed.
          let h55 := h44.left
          let h56 := h44.right
          -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
          have h57 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h53, we can now drive its conclusion.
          let h58 := h53 h57
          -- False on the left can always be used.
          apply False.elim h58
        case inr h59 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h60
          -- Implications on the right can always be decomposed.
          intro h61
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the left can always be decomposed.
          let h62 := h61.left
          let h63 := h61.right
          -- Conjunctions on the left can always be decomposed.
          let h64 := h60.left
          let h65 := h60.right
          -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
          have h66 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h62, we can now drive its conclusion.
          let h67 := h62 h66
          -- False on the left can always be used.
          apply False.elim h67
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h68
          -- Conjunctions on the left can always be decomposed.
          let h69 := h61.left
          let h70 := h61.right
          -- Conjunctions on the left can always be decomposed.
          let h71 := h60.left
          let h72 := h60.right
          -- We want to use the implication h69 based on <expert-advice>. So we show its premise.
          have h73 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h69, we can now drive its conclusion.
          let h74 := h69 h73
          -- False on the left can always be used.
          apply False.elim h74
  case inr h75 =>
    -- Disjunctions on the left can always be decomposed.
    cases h75
    case inl h76 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h77
      -- Implications on the right can always be decomposed.
      intro h78
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h79 := h78.left
      let h80 := h78.right
      -- Conjunctions on the left can always be decomposed.
      let h81 := h77.left
      let h82 := h77.right
      -- We want to use the implication h79 based on <expert-advice>. So we show its premise.
      have h83 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h79, we can now drive its conclusion.
      let h84 := h79 h83
      -- False on the left can always be used.
      apply False.elim h84
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h85
      -- Conjunctions on the left can always be decomposed.
      let h86 := h78.left
      let h87 := h78.right
      -- Conjunctions on the left can always be decomposed.
      let h88 := h77.left
      let h89 := h77.right
      -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
      have h90 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h86, we can now drive its conclusion.
      let h91 := h86 h90
      -- False on the left can always be used.
      apply False.elim h91
    case inr h92 =>
      -- False on the left can always be used.
      apply False.elim h92



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335711483038386452479283071403 : (p1 → (((p5 ∧ ((p3 ∧ ((p4 → p1) ∨ (p5 ∨ (p3 ∨ ((p5 ∨ False) ∨ p5))))) → ((p3 ∧ True) ∧ (p2 ∨ (False → p1))))) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



