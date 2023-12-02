variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111085078600445543121545406984 : ((((p2 ∨ (False ∧ ((p3 → (p1 → (False ∧ (p2 → p2)))) ∨ p4))) ∧ ((p4 ∨ (((p5 → p5) → True) → False)) → p3)) ∧ p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320259256765689579671916548298 : (p4 ∨ ((p5 → p5) ∧ ((True → (((p3 ∧ p2) ∧ (p3 → False)) ∨ (p2 ∨ ((p2 → ((p5 ∧ False) ∧ p1)) ∨ p3)))) ∨ (p1 ∨ (True ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112424626396658446308420667342 : ((((p4 → (((p3 → p2) ∨ (p2 ∧ (p4 → (False ∨ p1)))) ∧ (((p3 → (p1 ∧ (True ∧ p4))) ∧ p5) → p1))) ∧ p4) → p5) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51151770174936473448685406155 : (((((True → False) ∨ (p3 ∨ (((p1 ∧ p5) → ((p1 ∨ p5) ∨ p4)) → (p4 ∧ p4)))) → p3) ∨ ((p2 ∨ (p5 ∧ (True ∨ p5))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638375376623809033948968954795 : ((((((False ∧ p4) → ((p2 → p2) ∨ p4)) ∧ (((p2 → ((p1 → p5) ∨ p4)) ∨ p1) → ((p4 ∨ ((False ∨ p5) ∨ p1)) → p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328632119057181628564748868702 : (True → (((((p2 ∧ False) ∨ ((p3 ∧ p2) → ((p1 ∧ p5) ∧ p4))) ∧ p1) ∧ p2) → (p5 ∨ ((p4 → (p3 ∨ p4)) ∧ (p1 ∧ (p1 ∧ True)))))) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199310212435672917558497129425 : (((((p3 ∨ p4) → (p4 ∨ p1)) ∨ p1) ∨ p4) → (p1 → ((((p1 → True) ∧ ((((p2 → p1) ∨ p1) → False) ∨ p1)) ∧ True) ∨ (p1 → p1)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329693562203092195914800927173 : (True → ((p4 ∨ p1) → ((p5 ∨ p3) ∨ ((((p2 ∨ (p5 ∧ (p3 ∨ p3))) → ((True → p5) ∧ True)) ∨ True) ∨ (p2 → (p4 ∨ (p5 ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
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
theorem thm_5_vars_230288223760929132109915810654 : (((p1 ∨ True) ∧ p3) → (((p3 ∧ False) → True) → (((p4 → p4) → p1) → ((((p1 ∨ p4) ∨ (True → ((p1 → False) ∧ p3))) ∨ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
theorem thm_5_vars_193990071022244922421662052856 : ((p3 ∨ (p4 ∧ ((p1 ∧ (False → p3)) → (True ∨ p1)))) → (((((False → p3) ∧ ((True ∨ p2) ∧ p5)) → False) ∨ (True → False)) ∨ (p1 → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355667675255113687997934292668 : (p5 → ((((((p1 → (p2 → (p1 ∧ (p1 → p1)))) ∨ p4) → (((True ∨ ((p1 ∧ p4) ∨ p5)) → False) ∨ p3)) ∨ True) → p1) → (p1 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 → (p2 → (p1 ∧ (p1 → p1)))) ∨ p4) → (((True ∨ ((p1 ∧ p4) ∨ p5)) → False) ∨ p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180432046893629288348996693057 : ((((True → ((p1 ∧ (p1 → p2)) → (p5 → False))) → p2) → (False ∧ p2)) → ((((p4 ∨ ((p3 ∧ False) → True)) ∧ (p5 → p2)) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788368129353364490032212731117 : (((p5 ∨ (((p5 → ((False ∧ p3) ∨ ((p1 → (((p4 ∨ (p3 ∧ ((p4 ∨ p4) ∨ p4))) ∨ p1) ∨ p3)) ∧ False))) ∧ (p2 → p5)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_59485643457156135299222705507 : (((p1 → p4) ∨ ((p5 ∧ ((p5 ∨ (p3 → (p3 → (((p5 ∧ False) ∨ False) ∧ (False → False))))) ∧ ((p4 ∨ p4) → (False → p3)))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258814025309345831943844986852 : ((True → False) → (p1 → (p4 ∨ ((((p3 ∨ p3) → (((((False ∨ False) ∨ p1) ∧ (True → False)) ∨ (p2 → p3)) → p4)) → (True ∧ False)) ∨ False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47297701799245135962213359024 : (((((True → False) → True) ∧ ((p2 ∨ p1) ∨ ((((p1 ∨ p4) ∧ p5) → p3) → ((p2 ∧ ((p4 ∧ p4) ∧ p1)) ∧ p4)))) ∨ (p4 → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148277213874204366506017440327 : ((((((p5 → p4) ∧ (p3 → ((((p2 → p3) ∧ True) → p2) ∨ p1))) → p4) ∨ p2) → (p1 ∨ (p5 ∧ False))) ∨ (((p4 ∧ p2) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24863487844062343966406462070 : ((((p4 → p5) ∨ p3) ∨ (((((p5 ∧ p3) ∨ (p3 ∧ ((p5 → False) → True))) ∨ ((p2 ∨ p2) ∨ ((p2 ∧ p4) ∨ True))) → p5) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p3) ∨ (p3 ∧ ((p5 → False) → True))) ∨ ((p2 ∨ p2) ∨ ((p2 ∧ p4) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327956053679201363751136227279 : (True → (((p2 → (p4 → (p3 ∧ (((p1 → (True ∧ (p5 → p3))) ∨ p5) ∨ (False → p1))))) ∨ ((False ∧ False) → (p3 → p4))) → (p3 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_576877698395587081731515099928 : (((p3 → ((p4 ∨ (((True ∧ p4) ∨ ((p5 ∨ p2) ∧ p5)) → ((p5 ∨ True) ∧ ((((p2 ∧ p4) ∨ (p2 → p4)) ∨ False) ∨ p5)))) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254590154081654946317852490789 : ((p3 ∧ p1) → ((((p4 → p4) → p4) ∧ (p2 ∧ (((p5 ∧ False) → (True ∧ p5)) ∨ (True → (p1 ∧ (p3 → p2)))))) → (p3 ∧ (p4 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h20 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h22 := h13 h20
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h26 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h28 := h13 h26
    -- One of the premise coincides with the conclusion.
    exact h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h2.left
  let h30 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h30.left
  let h32 := h30.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h1.left
    let h35 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h31
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201170494028720628127703622747 : ((p1 → ((p2 ∧ (p1 → (p4 ∧ p4))) ∧ p3)) → (True ∧ (((((p4 ∨ p1) ∧ True) ∨ True) ∨ ((p4 ∨ ((p5 ∨ p3) → p4)) → False)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_445265452637354896786673169400 : (((((((True ∨ p3) → p4) ∧ ((p1 ∧ (p3 → (p2 ∧ (False ∧ (p3 ∨ True))))) → ((p1 → p4) → p1))) ∧ p3) → (p4 ∨ (True ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605602704979688987407867839788 : ((((p4 → (((True → (True → ((((p2 → True) → p3) ∧ p2) → False))) → (((p5 ∨ ((p5 ∧ p1) ∨ False)) ∧ True) → p3)) ∨ p1)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698077424579034425196413954203 : ((((((p2 ∨ True) → ((True ∨ ((p1 ∧ p2) → False)) → p5)) ∨ p3) ∨ ((((False ∧ p4) → False) ∧ ((True → p2) → (p2 ∧ p2))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152622227079975275769793306541 : (((False ∨ p4) ∧ (p4 → (p2 ∨ (((((p1 → True) → p4) ∨ p4) → ((False ∧ p1) ∧ (p1 ∧ p5))) → p2)))) → ((p4 → p1) ∨ (True ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189662939497473961848304074767 : ((p2 ∨ ((p5 ∧ (p4 ∧ (p5 ∧ p3))) → (False ∨ True))) ∧ ((((p3 → (False ∨ p3)) ∨ (p4 ∧ (p1 ∧ True))) → p2) → (p4 ∨ (p1 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : ((p3 → (False ∨ p3)) ∨ (p4 ∧ (p1 ∧ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250733196620249907046073462862 : ((p1 → False) ∨ (p4 ∨ ((p3 ∨ (p4 → ((((p1 ∧ p4) → ((p3 ∨ p2) → p2)) ∧ p2) ∨ (p1 ∨ (p1 → (p4 ∨ (True ∧ p3))))))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165794727632691826838963426241 : ((((p4 ∧ p4) ∧ p2) ∧ ((((True ∧ p2) ∨ (p2 ∧ p4)) → ((p1 → p4) ∨ True)) ∧ p1)) ∨ (((True → (p3 → False)) ∧ (p3 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56379117636815779493478324471 : (((((True ∧ p2) ∨ p2) → p4) → (p4 ∨ ((p5 → ((p4 → ((((True ∧ p3) ∧ p2) ∨ p4) → (p2 → True))) ∨ (p3 ∧ p2))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174660218273315393590754815598 : ((((p4 → True) → p5) ∧ (p1 → (p4 ∨ (p1 ∧ (p3 ∨ ((p1 ∨ p4) ∨ p3)))))) → ((((p3 → p4) ∧ p2) ∨ p2) → ((True ∨ p2) ∧ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h16
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h24 := h20 h22
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119574536137342009416899274192 : ((p5 → (((True ∨ (p2 → p5)) → True) → (p5 → (((p2 ∧ p4) ∨ p1) ∨ ((p5 ∧ ((p5 → p1) ∧ p3)) ∨ (True ∧ False)))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2183655870479498058612495466 : (((p2 → (p1 ∧ ((((p5 ∧ True) → (p1 → (p4 ∨ False))) ∨ p3) ∧ p5))) → p2) ∨ (p3 ∨ ((((p1 → p2) ∧ p5) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_46885604883888947090185364782 : (((((((((p1 → ((p3 ∨ p4) ∧ ((True → (p3 → p2)) → False))) ∧ p3) ∧ (p4 ∨ True)) ∧ True) → False) ∨ p3) ∨ True) ∨ (p1 ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313386443358763436904172423135 : (p3 ∨ ((((((p4 ∨ (False ∨ True)) ∧ ((True ∨ ((p1 ∨ p1) ∨ p3)) → (((False ∨ p5) → True) → p5))) ∧ True) ∧ (p5 → p3)) ∧ True) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ ((p1 ∨ p1) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : ((False ∨ p5) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ ((p1 ∨ p1) ∨ p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h20 := h9 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((False ∨ p5) → True) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h23 := h20 h21
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592863518494159000401269416600 : (((((((False ∧ p3) ∨ (p4 ∧ p5)) ∨ ((p1 ∨ ((p4 ∨ (p2 ∧ p1)) → ((p3 ∧ p4) ∨ False))) → False)) ∧ (p1 ∨ (p1 ∨ False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339021781869262786018117850935 : (p1 → (True ∧ ((((p2 ∧ (p2 ∧ p5)) → p5) → p2) ∨ ((((p2 ∨ False) ∨ (p5 → ((p5 ∨ (p5 ∨ p2)) ∨ (p4 → False)))) ∨ p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147150955573394526063278503479 : (((p2 ∧ ((p2 → p4) → (p2 ∨ ((p3 ∧ p5) ∧ (((p4 ∧ p2) → (p1 ∧ (False ∨ p3))) ∧ True))))) ∧ p2) ∨ ((p2 → p1) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115037182707053242592628856211 : (((((p5 → (p2 → p2)) → (p5 → (p3 → (p1 ∨ p5)))) ∧ False) ∨ ((p4 ∧ p4) ∨ ((((p2 → p1) → True) ∧ p4) ∨ True))) ∨ (p2 ∨ p5)) := by
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
theorem thm_5_vars_165711510594726039447821206274 : ((((False ∨ (p3 → p2)) → False) ∧ ((p3 ∧ (False ∨ ((p5 → (p2 ∨ p3)) → True))) ∧ p2)) ∨ (p3 → ((True → p5) ∨ (True ∨ (False ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51726827960972832423733960290 : ((((((p1 → p5) ∧ p4) → True) ∧ ((p1 ∧ p3) ∨ ((True ∨ True) ∧ (p4 ∧ p1)))) ∧ (p1 ∧ (p1 → ((p3 → (False → True)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616024705122498061493248131672 : ((((((False → (p3 → p2)) ∨ (p1 ∨ (((p3 ∨ p1) → False) ∨ (p2 ∧ p3)))) → (((p3 → p1) → p5) ∧ (True ∧ (p5 ∨ p4)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190408548390940482302571870624 : (((p5 ∧ (p3 ∧ ((p3 → (p1 ∧ p1)) ∧ False))) ∨ p3) ∨ (p2 ∨ (((p4 ∧ p2) ∨ (((True ∧ (p1 → True)) ∧ (p3 ∧ False)) ∨ True)) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347374669665083821153561334014 : (p3 → (((p4 ∨ (p2 ∨ ((p5 ∧ False) → p5))) → p5) ∨ ((p4 → p3) ∨ ((True ∧ (((False → p1) ∧ (False ∧ p2)) → p3)) ∧ (p4 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161693642102881766751509530895 : ((p2 ∨ (((p2 ∧ False) → (p1 ∧ (False → False))) ∧ (((True → p3) → (p5 → p4)) → (True ∧ True)))) → ((p1 ∧ (p1 → p1)) ∨ (p4 → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65354451282536079302954390153 : ((p3 ∨ ((((((p1 ∨ p1) ∨ p5) ∧ (p1 ∧ False)) ∨ (False → p1)) ∨ (p1 ∧ p5)) ∨ (((p2 ∨ p5) ∧ (p4 ∧ p4)) → (p1 ∧ False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342569472346116509115375809008 : (p2 → (((((False → (True ∨ (True ∧ False))) → False) ∨ p4) ∧ (p3 ∧ p5)) ∨ ((p1 → (((p3 → p1) → p1) ∨ ((p5 → False) → p3))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111965184105792574777509354951 : ((((p3 → ((((p5 ∧ p5) ∨ False) → p4) ∨ p3)) → ((True → (p4 ∧ (p3 → (p4 → (True ∨ True))))) ∧ (p2 → p2))) ∨ p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41960445699844894784255270290 : ((((p4 ∧ p4) ∧ (((((((((p2 → p5) ∨ p3) ∧ p5) ∧ p1) ∧ p2) ∨ False) → (True → False)) ∧ (p1 ∨ (False ∧ p1))) ∨ p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181066971462592990563337230483 : (((False ∨ True) → (((p5 ∨ p2) ∨ (p1 ∧ p1)) ∨ ((p1 ∨ p4) ∨ p4))) → (((p2 ∨ p4) → (p5 ∨ (p2 ∨ p2))) ∨ ((False → p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180625674096551815555818986346 : (((True → ((p5 ∨ p4) ∧ (p1 ∧ p4))) ∧ ((p1 ∧ True) ∧ (p3 ∨ p3))) → ((p3 → (p5 ∧ ((p4 ∧ (p1 ∨ (p5 ∧ p4))) ∧ p5))) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504585372638648089316628539117 : ((((p1 ∨ (p5 → p3)) → ((((((p3 → (p1 ∨ (p5 ∨ False))) ∧ ((True ∧ (p4 ∨ p4)) ∧ False)) ∨ p3) ∨ p4) → (p1 → p2)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42582437684279186611375545908 : (((p2 ∨ ((((((False → False) → (p5 ∧ p2)) ∧ (p4 ∨ (p3 ∨ p4))) ∨ p5) → p2) → (p5 → (True → (p5 → (p4 ∧ True)))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65643078713031907000077457596 : ((p4 ∨ (((p1 ∧ ((p5 → p4) ∨ p2)) ∧ (((p1 ∨ (((((p4 ∧ p1) → (True → p1)) ∧ True) ∨ p1) ∧ p4)) → p1) ∨ p1)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305678037546152000284455926655 : (p1 ∨ ((((p1 → (False ∧ p2)) ∧ p3) ∨ ((p5 ∧ p4) → p2)) ∨ ((((((p3 ∧ p3) → p3) → p5) ∨ (p3 ∨ p3)) → (p3 → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112859625657972155192219939562 : (((((p1 → False) → p3) ∨ ((p1 ∧ (((p3 → (p5 ∧ p2)) ∨ False) ∧ (p4 ∨ (False → (p5 ∨ p1))))) ∨ (p3 ∨ p1))) → p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173209806993114872433327878911 : ((p5 ∨ (((p2 ∨ p1) → (p1 → True)) ∧ (p3 ∧ ((p4 → p3) → (p2 ∧ p1))))) ∨ (((p3 ∨ (((False ∧ p3) → p5) → p5)) ∧ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732120386612874371359644466174 : ((((True ∧ p2) ∧ (p2 → (((p3 → (p3 ∧ ((False ∧ ((p5 → p3) ∨ p1)) ∧ p2))) ∧ ((True ∧ p2) → p3)) ∨ ((p5 → p5) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160977348976054672165898146033 : (((True → (p2 ∧ False)) ∧ (((p1 ∨ (False ∨ False)) ∨ (p3 ∨ p4)) ∨ (((False ∨ p1) ∧ p2) ∨ p1))) → (p4 ∨ (((p1 ∧ p4) ∨ True) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- We need to get the right conjuct of h8 based on <expert-advice>.
        let h9 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h26 := h2 h25
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h30 := h2 h29
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244139868175177821677148073336 : ((True ∧ p4) ∨ (((((p1 ∧ False) → p1) → (p1 ∧ (((p1 → False) → (p1 ∨ p2)) ∧ p4))) ∨ (p1 ∧ (True ∧ (True ∧ False)))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315022510405020640767743128270 : (p3 ∨ (((p5 ∧ p5) ∨ ((p5 ∧ p1) ∨ (p4 → p5))) ∨ ((p3 → True) ∧ (True ∨ ((p1 ∧ p2) ∨ ((p3 ∨ p1) ∧ ((p4 ∨ p4) → p3))))))) := by
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
theorem thm_5_vars_61264246370788708667458570077 : ((False ∧ (p1 ∨ ((p5 ∨ (((True ∨ ((((p5 → False) → p4) → (((p3 → (p2 → p3)) ∨ p1) ∨ p4)) → False)) ∨ p4) → p3)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657453922124470651725651866375 : (((((p3 ∧ False) ∨ (p5 → (((True → ((p5 ∧ ((False ∨ p5) ∨ (p1 ∨ p5))) ∧ (p2 ∨ p1))) ∨ p3) → (p2 ∧ p1)))) ∨ (p4 → p4)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_185266373036103978146805221825 : ((p1 ∧ (True ∧ (False ∨ (((p5 ∨ True) → p2) → (p5 ∨ p1))))) ∨ ((((False → ((p2 ∧ False) ∧ p3)) ∧ ((p3 → True) → p4)) → p4) ∨ p5)) := by
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
  have h4 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313241405413290542475626598413 : (p3 ∨ (((p3 ∨ p4) ∨ ((((True → ((p3 → (p2 ∧ True)) ∧ p5)) ∧ ((((True ∧ p2) → p5) ∧ False) ∧ p5)) → p2) ∧ (p4 ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208842919026931227706251676491 : ((p3 ∧ (True → (True → (False → True)))) → ((p2 → ((p4 ∨ p4) ∧ (p5 ∧ (False → True)))) ∨ ((p3 ∨ (True → p1)) ∨ (p1 ∧ (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205798288387587587300822726713 : (((p1 ∨ p5) → ((p5 ∨ p3) ∧ p3)) ∨ (((p2 ∧ (p2 → (((True → ((p5 ∨ (p2 → False)) ∨ p2)) → p5) ∧ False))) ∧ p1) → (p4 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322403298347115206804743814586 : (p5 ∨ ((((((p3 → p1) → (p1 ∨ (p5 → (p2 → p1)))) → p2) ∨ True) ∨ (p1 ∨ (((p3 ∧ ((p3 ∨ True) ∨ p1)) ∧ p4) → p2))) ∨ p1)) := by
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
theorem thm_5_vars_300537588768223776563148725911 : (False ∨ ((((((p4 ∧ p2) ∨ False) ∨ p4) ∨ ((((False → True) ∨ (False ∧ (p2 ∨ False))) ∨ p2) ∧ False)) ∨ p4) ∨ ((False ∨ True) ∨ (p1 ∨ p5)))) := by
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
theorem thm_5_vars_149797432927288012108728650633 : ((False ∨ ((p1 ∧ p1) → (((p4 → p1) → p4) ∧ ((p2 → p3) → (False ∨ (((p2 ∧ p3) → True) ∨ p2)))))) ∨ ((True → (False ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738749624686526723245947067901 : ((((p2 ∧ p3) ∨ (((False → p1) → ((((p2 → (False ∨ True)) ∧ p4) → p2) ∨ ((p4 ∨ True) ∧ (p3 ∧ p5)))) ∧ (True ∨ (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689392653252234332764538578935 : (((((((p2 ∧ p2) ∨ (p2 ∨ p3)) ∨ (p2 → (p4 → (True → True)))) → (p4 ∧ p2)) ∨ (((p1 → (False → False)) ∨ p5) ∧ (p3 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167560582505295484877959438768 : ((((((True ∨ p4) ∨ (p2 ∧ p2)) → (p5 ∨ (p4 ∧ (p5 ∨ p2)))) → True) ∨ (p1 ∨ p4)) → (((p4 ∧ (p3 ∧ p5)) ∧ (p1 ∨ p5)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47144215115410769902459047636 : (((((((p3 ∨ ((p3 ∧ (p4 → (p4 → True))) → p1)) ∨ p2) ∨ (p4 → True)) ∨ True) ∨ (((True → True) ∨ p3) ∧ p4)) ∨ (False ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115233574050872207308367641108 : (((((p2 → True) → (((False ∨ p2) ∨ p3) ∨ p1)) ∨ p1) ∨ ((p3 ∨ p2) ∧ ((p5 → False) ∨ (((p1 ∧ p1) → p4) ∨ False)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61798651311037622697441583690 : ((p2 ∧ ((((p3 ∨ (p3 → ((p3 ∧ False) ∨ (((True ∧ (p2 ∧ ((False ∧ (p3 ∨ p3)) → p1))) ∧ p3) ∨ p1)))) ∧ p3) ∨ p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191900222718173789760081848161 : ((p5 ∨ ((False → ((False → True) ∨ p3)) ∧ (p4 ∨ p2))) ∨ (p1 → (((p5 → p4) → False) ∨ (((p3 ∧ p1) ∧ p3) ∨ ((p3 ∨ False) ∨ True))))) := by
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
theorem thm_5_vars_728682216177106080085469963130 : ((((p5 → (p1 ∨ p2)) ∨ (((p3 ∧ (p1 → False)) ∧ ((((p5 ∨ ((False ∧ p2) → p1)) → p4) ∨ (p4 ∨ p3)) ∨ True)) ∧ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63961517797996716881361419265 : ((False ∨ (((((p3 → ((p2 → p2) → True)) ∨ False) ∧ ((((p4 ∧ True) ∨ ((p5 ∨ (False ∧ False)) ∨ p2)) ∨ p3) ∧ p4)) ∧ True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669663757335208847756917049804 : (((((((False ∨ (((((p5 → (p1 ∨ True)) ∨ True) → p4) ∨ p2) ∧ p1)) ∨ p3) → True) → (p4 ∨ (p4 ∨ p2))) ∨ (p1 → (True → p1))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116068266661809080824956793322 : ((((p3 ∨ p1) ∧ False) ∧ (((p3 → p4) ∨ (p5 ∨ (p1 ∨ (p4 ∨ False)))) ∨ ((True ∨ (p2 → p2)) → ((True ∨ True) → True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330960650912959169341402558150 : (True → (p5 → (((p5 → False) → ((p3 → p5) → (((p5 ∧ (p3 ∧ (((False ∨ False) ∧ (p2 → p1)) ∨ (True → p3)))) ∨ p2) ∨ p2))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317622664505060674687528735400 : (p4 ∨ ((((True ∧ (((p2 ∨ ((p1 ∨ p4) ∧ p3)) ∨ ((True ∧ p1) ∧ (True → (p3 ∨ (False → True))))) ∨ (p1 → p1))) → p4) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190860426756284352846676111961 : (((((False ∧ True) ∧ (True ∧ p1)) → p4) → (False ∧ True)) ∨ ((((False → p2) ∧ (p1 ∧ p4)) ∧ (((p2 ∨ True) ∨ (p2 ∨ p1)) ∨ p4)) → p4)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136890834965341462599285669669 : (((p3 ∨ p2) ∨ ((((p1 ∨ p4) ∨ (p1 ∧ (p5 → p2))) → (True → True)) ∧ ((p5 ∧ p3) ∨ ((p5 ∨ p3) → p2)))) ∨ (True → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329042357571532876281443312160 : (True → ((p2 ∨ ((p4 ∧ (p3 ∨ p5)) ∨ p2)) → (((p3 ∨ ((((p1 ∨ (False ∧ p4)) → (p1 ∨ p3)) → p5) → p2)) ∨ True) ∨ (p5 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50246609370385194754653053620 : ((((((p3 ∧ ((p5 ∨ p4) → True)) ∧ p3) ∧ (p5 ∨ ((p4 → (p1 → p2)) → (False → p1)))) → False) ∨ (p5 → ((p2 → p2) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258931436284308772116017711804 : ((True → p2) → (p3 ∨ (p1 ∨ (((p3 ∧ (p5 → p1)) ∨ ((((p1 ∧ p1) ∨ p1) → p2) → (p1 → (p2 ∨ (False ∨ (p4 → p2)))))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207812960599161448276075068666 : (((p3 → ((True → p4) ∨ p3)) → p3) → (((p4 ∧ ((p3 ∧ (((True ∨ p3) ∧ p2) → (p3 ∨ (p4 → p3)))) → p5)) ∧ (p4 ∨ p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((True → p4) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2752353237552199913923346998 : ((False ∨ (p5 ∨ (False → p3))) ∧ (((((False ∨ (p3 → p2)) ∧ p3) ∧ (p1 → p5)) ∨ (False → p4)) ∨ (False → ((True → p4) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316872780608863159416638694259 : (p3 ∨ (p1 → ((((p4 ∨ ((False ∧ (False → p3)) → (p4 → True))) → (p5 ∧ False)) ∨ True) ∨ (p3 ∨ (p4 ∨ (True ∧ (False ∨ (p4 ∨ p5)))))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205274794840799937455451400458 : ((((p2 → True) → False) ∨ (p1 ∧ p4)) ∨ (True ∧ (p3 ∨ ((p1 → ((p4 ∨ p1) ∨ (True ∧ (p3 → False)))) ∨ ((p3 → (p3 ∨ True)) ∧ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149079636430418925835966891610 : ((((p2 ∨ p3) → p4) → ((p5 → False) → (((False → ((p5 → True) ∨ p5)) ∧ (p1 → p5)) ∨ (p1 ∨ p4)))) ∨ (((p5 ∧ True) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167100330109559511324110574541 : (((((p4 ∨ p3) ∨ (((p3 ∧ False) ∨ (p5 → p1)) ∧ (p1 ∨ p5))) ∨ (True ∨ p1)) ∨ False) → ((p1 ∨ (p1 ∨ False)) → (p5 ∨ (True ∨ p4)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h17 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h28 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h32 =>
              -- Conjunctions on the left can always be decomposed.
              let h33 := h32.left
              let h34 := h32.right
              -- False on the left can always be used.
              apply False.elim h34
            case inr h35 =>
              -- Disjunctions on the left can always be decomposed.
              cases h31
              case inl h36 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h37 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h37
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41
    case inr h42 =>
      -- False on the left can always be used.
      apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315105512325921693546727288935 : (p3 ∨ (((((p5 → p3) ∨ False) ∧ False) ∧ p4) ∨ (p3 ∨ (((True → (p4 ∧ p1)) ∧ p3) → (p4 ∧ ((p5 ∧ ((False ∧ p5) → False)) ∨ True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201836274546472450075949277452 : ((((p1 ∧ False) ∨ (True ∧ p4)) ∨ True) ∧ ((True ∧ (p5 ∨ ((p4 ∨ True) ∧ ((True ∨ p5) ∧ p1)))) ∨ ((p3 → p3) ∨ (p5 ∨ (True → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_148885595143092613595930187037 : ((((p2 ∧ p1) ∧ (p4 ∧ p5)) ∨ ((((p1 → p5) ∧ (p3 ∧ p1)) ∨ p2) → (False ∨ (p5 → (p1 → p5))))) ∨ (p1 ∧ ((p2 ∨ False) → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354311977943064621730783858737 : (p5 → ((((((True ∧ p1) ∧ (True → p2)) → (((p3 → (p3 ∧ (p5 ∧ p5))) → True) ∨ p1)) ∨ p3) → (((p2 → p4) ∨ True) ∨ False)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650908332547535125673514010477 : ((((((p1 ∧ p4) → ((p4 → p3) → False)) ∧ (p3 → ((((p3 ∨ (p2 ∧ (False → (True ∧ p1)))) ∨ False) → p5) → p1))) ∧ (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623650674979941223359838327675 : ((((p1 ∨ ((((p3 ∧ (False → p3)) ∨ (((p1 ∧ (p5 ∨ True)) ∧ p3) → p3)) ∧ ((False → (True ∨ (True → p2))) → p5)) ∧ p3)) ∨ True) ∨ p2) ∧ True) := by
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



