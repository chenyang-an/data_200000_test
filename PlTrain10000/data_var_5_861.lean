variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39112186860483255429388593192 : ((((p4 → p2) ∨ (((False ∧ p1) ∧ ((p1 ∧ (p3 → p4)) ∨ (((True ∨ True) ∧ (True ∨ (False → (p4 → False)))) → p2))) ∧ True)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164919328746238413566455747538 : (((((p1 → ((p2 ∨ ((p4 → p5) → ((p3 → False) ∧ True))) ∨ p4)) ∧ True) ∨ False) → p2) ∨ (p5 → ((p3 ∨ ((p1 ∧ p4) ∧ True)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350254407411012762268801034241 : (p4 → ((p1 ∧ ((p3 ∨ ((((p2 ∧ ((True ∨ p2) ∨ (p1 ∨ p1))) ∨ p3) → ((p5 ∨ p1) ∨ ((p2 ∨ True) ∧ p3))) ∨ p5)) → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205519703016155930710122944123 : (((True ∨ False) ∧ ((True ∨ p5) ∧ p2)) ∨ ((((True → ((p2 → (p5 ∨ (True → False))) ∧ True)) → (p1 ∧ (p2 ∨ p2))) ∧ p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48509533055153942178584198273 : ((((((((False → (p2 ∧ True)) → ((p3 → p2) ∧ p4)) → p5) ∨ ((p3 ∨ p2) ∨ p3)) ∧ (False → False)) ∨ p4) ∧ ((False → p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110391310075054087892363558035 : ((p3 → (((False ∨ (p2 ∨ (False → False))) ∧ (p1 → ((p3 → (False ∨ p4)) ∧ (False ∨ p3)))) ∨ (p1 → (True ∨ (p2 ∨ p2))))) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38218563398218100494042523966 : (((((p3 ∨ (p5 ∨ p5)) → ((p4 → (True ∨ ((False → False) ∨ (True → p4)))) ∨ (p3 ∨ (True ∧ p4)))) → ((True → False) → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111136709557045030718780086467 : ((((True ∧ (((p5 → False) ∨ False) → (True ∧ p2))) → ((p5 ∧ p1) ∨ ((p1 → (((False ∨ p2) → p2) ∧ p4)) → p4))) ∧ p3) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172846127022467000965554466117 : ((False ∧ ((p3 ∨ (p5 → ((p4 ∨ (False ∧ p4)) → (True ∧ p1)))) → (p5 → p4))) ∨ ((((p1 → p3) → ((True → p3) ∨ p2)) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617669462852901640408528945910 : (((((((p2 ∧ p3) → (p3 → p2)) → p4) ∨ (p3 → ((False ∧ (((p4 ∧ (False ∧ (p3 → (True ∨ p1)))) ∨ p2) ∨ p3)) ∨ True))) ∨ p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_773434201860639999300677725963 : (((False ∨ ((((((False ∨ True) → ((p5 → (p4 → (p3 ∨ (p3 ∨ p5)))) ∧ p1)) → ((p5 → False) ∨ (p2 → p3))) ∨ True) ∨ p3) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42121876149369046818691740739 : ((((True ∨ p3) → (True ∧ (((False ∨ ((((((p3 ∧ p3) ∧ p3) ∧ (p5 → False)) ∨ (p3 ∨ p5)) ∧ p5) → False)) ∨ p3) ∨ p4))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714056717501147719103354776113 : ((((((p3 ∧ (p2 → p3)) → p4) → p5) → ((p1 ∧ (True ∨ (((p2 → p2) → False) → p5))) → (((p5 ∧ (True ∨ p3)) → False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112296357064515871794476364161 : (((p1 → ((((p5 ∨ False) ∧ (((p2 → True) ∧ (p2 ∧ p3)) → (((p3 → p1) ∨ p1) ∧ p4))) ∨ (p4 ∨ p3)) → p3)) ∨ p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354869819090654779380834217110 : (p5 → ((True ∧ (True → (((p4 ∨ ((p3 → ((p2 → True) → False)) ∧ (p1 → (True ∨ p3)))) ∨ (((False → p4) → True) ∨ p3)) → p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42674843735066988438618421447 : (((p4 ∨ (p5 ∧ ((((p4 ∧ ((p5 → p3) ∨ (p5 ∨ (p3 ∨ p3)))) ∨ (p1 ∧ ((p3 ∨ p3) ∨ p4))) → False) → (p5 ∧ False)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219748356501917538926985642491 : ((p2 → ((p2 ∧ p2) ∧ True)) → (((True ∨ p5) → (p3 → ((((False ∨ p5) ∧ ((p4 → False) ∧ p5)) ∨ p4) ∧ (p3 ∧ p4)))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739415654811980240122358582126 : ((((p5 ∧ True) ∨ ((((p2 ∧ p3) → (((p1 ∨ ((p1 ∧ True) → p2)) → True) ∧ (p4 ∧ False))) ∨ ((p1 → p3) → p2)) ∧ (p1 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111880601156254641951730003823 : (((((p3 ∧ p2) ∨ (((((p1 ∧ True) ∧ p5) ∨ True) ∨ (True ∧ (p5 → p4))) ∧ p2)) → (p3 ∧ ((p2 ∧ p5) → p3))) ∨ p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166901032547385248270432912162 : ((((p5 → (False ∨ (p2 → ((p5 → p5) ∧ p2)))) ∨ ((False → p2) ∧ (p2 ∧ p1))) ∧ p3) → ((p1 ∧ (p4 → ((p2 → p5) ∧ p4))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157349093046237727849328030229 : (((p5 ∨ ((p4 ∨ (((True ∧ p4) → (True → p2)) → (p1 ∨ p4))) → ((p1 ∨ True) ∨ p1))) → False) ∨ (p4 → ((p4 ∨ False) ∨ (p4 ∨ p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354893808144953750120359849371 : (p5 → ((p4 ∧ ((p4 ∨ (((False → p2) ∧ (True ∨ (p1 → ((((p2 ∨ True) ∧ p1) ∨ p4) ∨ False)))) → ((p2 ∧ True) ∨ False))) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230354652291089918253805071890 : (((p2 ∨ p4) ∧ p2) → ((False ∧ (((((p4 → ((p2 ∨ p4) → ((False ∨ p1) ∨ p5))) ∧ p1) ∧ p3) ∨ (p3 ∨ False)) ∧ p4)) ∨ (p4 → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136784717310248224125800010155 : (((False → p2) ∧ ((((p5 → ((p4 → p1) → p1)) ∧ (p3 ∧ (p5 ∧ ((p4 → (p1 → p5)) ∨ True)))) → False) → False)) ∨ (p4 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68977320546107407782276597753 : ((p4 → (p5 → ((((True ∧ (p3 → True)) → ((p3 → p4) → p1)) → (p3 → ((False ∧ ((True → (p2 ∨ p3)) ∧ p5)) ∧ p2))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113160700006706363408573297596 : (((p4 → ((p4 ∧ p5) ∧ (((p3 → (p3 ∨ (False ∧ p4))) ∧ True) → (p5 ∨ (p1 ∨ (True → ((True ∨ True) ∧ p1))))))) → False) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617354949794394968065781713142 : (((((((True ∨ p5) ∨ p5) ∧ (p1 ∨ (False → p4))) → (((False ∨ p1) ∧ (((p2 ∧ ((p5 ∧ p5) ∨ False)) → p5) ∨ p4)) → p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55530574167054652073181487727 : ((((p2 ∨ p1) → ((False ∧ p1) ∧ False)) → (p5 → ((((p4 ∧ (True → (p1 → ((p4 ∨ p4) ∧ False)))) ∧ p2) ∨ p4) ∨ (p1 → p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261438090461798705795981835691 : ((p5 → p2) → (((True ∧ p4) ∨ ((False ∨ (p2 ∨ ((p3 ∨ (True → p5)) ∨ (p1 → (False ∨ (p4 ∧ (p2 → p2))))))) ∧ (True → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191590438771074500811752208950 : ((p2 ∧ (p1 ∨ (p3 → ((p3 ∨ False) → (p2 → p4))))) ∨ (((((p4 ∨ (p5 ∧ (p5 ∨ p2))) ∨ (p5 → p3)) ∧ (True ∧ p3)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190363102778772281776254340676 : ((((p5 ∨ p2) ∧ (p1 ∨ (p5 ∨ (p1 ∨ p4)))) ∨ False) ∨ ((True ∨ (p4 ∧ p4)) → (p2 ∨ (False → (p3 ∧ (((False ∧ True) ∨ p1) → p3)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64612043704437339522555216549 : ((p1 ∨ ((p4 → False) → ((((False ∨ p5) ∨ True) ∨ (p4 ∨ ((False ∨ p2) → p5))) → ((p1 ∨ ((p3 ∧ True) ∨ (p5 → p4))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227853034861489847647018041074 : ((p2 ∧ (False ∨ p3)) ∨ (((p5 → p4) → (((p2 → p4) → p3) ∨ ((p2 ∧ True) → ((((p3 ∨ True) ∨ True) ∧ p2) ∧ (p1 ∨ p2))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324922113568968135749195593551 : (p5 ∨ ((p5 ∧ p5) ∨ (p1 → (p5 ∨ (((p3 ∨ ((((True ∨ p1) ∧ True) → False) → (False ∧ False))) ∧ (p1 ∧ True)) ∧ (p2 ∨ (True ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ p1) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∨ p1) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16615890880907035144316020796 : (((((((True ∨ (((p3 ∧ p3) ∧ p4) → (p4 ∧ True))) ∨ p3) → (p5 ∨ False)) → (p4 ∨ (p2 → False))) ∨ p1) ∨ (True ∨ (True ∧ False))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712363223085262070077777954198 : (((((p5 → ((p2 ∧ p1) ∧ p3)) → p4) ∨ (((p5 ∧ (p3 → ((False ∨ p4) ∧ ((p2 ∧ p4) → p2)))) ∨ (False ∧ p4)) → (p2 ∨ p5))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111298199188977281253067027188 : (((True ∧ ((p5 ∨ True) ∧ ((p5 → (p3 ∧ p1)) → ((((((p4 → (True → False)) → False) ∧ p1) → False) ∧ True) ∨ p1)))) ∧ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171424912983933356540286221251 : ((((p1 → False) ∧ ((p1 → True) ∧ (p1 ∨ (True → (False → (True → True)))))) ∧ p3) ∨ (False ∨ ((((p3 → (p5 ∨ p1)) ∨ True) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_137631982487694931343538329294 : ((False ∨ ((True → ((((p5 → True) ∨ p1) → p2) ∧ ((True ∨ ((p4 ∨ (p4 ∧ p1)) ∨ p4)) ∨ p3))) ∨ (p1 ∨ p1))) ∨ (p3 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149248090337764657485735142059 : (((p1 ∨ p4) ∨ ((((p3 ∧ ((False → p3) ∨ p5)) ∧ p2) ∨ False) → (((True ∧ p4) ∧ p1) ∨ (p1 ∨ p5)))) ∨ (((p1 ∧ p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185818521241929417000540918511 : (((((((p2 ∨ p3) ∧ (True ∧ p3)) ∨ True) ∨ p1) ∧ True) ∧ p5) → ((((p1 ∧ ((True ∧ p4) ∧ p2)) ∨ p4) ∧ (True → True)) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h9.left
        let h15 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47442249533439313529787690355 : (((p3 ∧ (((p1 ∧ (((p1 ∧ (True ∧ p4)) ∧ (p5 ∧ (True ∨ p2))) → p3)) ∧ (p5 → (False ∧ p4))) ∧ (p5 ∨ p5))) ∨ (True ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255752326885260098150406305779 : ((True ∨ True) → ((((((p1 → p4) ∧ p5) ∨ p5) ∧ p3) → p2) ∨ (((((True ∧ p2) ∨ (p5 ∨ (p4 ∨ (True ∨ p3)))) ∨ p1) ∧ p1) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738287135262082114137793279531 : ((((False ∧ p5) ∨ ((p3 ∧ (p4 → p3)) ∨ ((p5 ∧ False) ∨ (((False → (((False ∨ (p4 ∨ True)) ∧ p3) ∧ False)) ∧ (True → p5)) → p5)))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54337909734945725955030189750 : (((p5 ∧ (((False → (p5 → p2)) ∨ p3) → False)) ∧ ((False ∨ p1) → ((p5 → ((p4 ∨ ((p3 ∧ p3) → False)) → p1)) → (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55904265217765198402667921751 : (((p4 ∨ ((p1 → p5) → p2)) ∧ ((False ∧ (((((p2 ∨ ((p3 ∧ p5) → (p3 ∨ p4))) ∨ True) ∨ p3) ∧ p1) ∧ p2)) ∨ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263402218068806986190318828609 : (True ∧ ((((p5 ∧ (p2 ∨ (p2 ∨ p1))) ∧ p4) ∧ (((((p3 ∧ (p5 ∨ p2)) → p3) → p2) ∨ (True ∧ p4)) ∨ False)) ∨ (True ∧ (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116440590743196517521127109866 : (((p3 → (p5 ∧ p2)) → (((p3 ∨ p5) ∧ (False → (p5 ∧ (p4 ∨ ((p1 ∧ False) → False))))) ∨ (p2 ∨ ((p2 ∨ p3) ∧ p3)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587006637873222346318773424477 : (((((p4 ∨ (p2 → (((p1 → p2) ∨ ((((True ∧ (True → (p5 → p3))) ∨ False) ∨ ((p3 ∧ p3) → p4)) ∨ True)) → p1))) ∧ p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47079740226090061085078425654 : ((((((((False ∧ p5) ∧ (p1 ∨ p5)) ∨ (p5 → (p1 ∨ ((True ∧ p3) ∧ p1)))) → (p1 → p3)) → p4) → (True ∧ p3)) ∨ (True ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118217400495989802321338565667 : ((p1 ∨ ((((p4 → ((p1 ∨ p3) ∨ ((p1 ∧ (True → ((p3 ∧ p3) ∧ p5))) → ((p4 ∧ True) → p1)))) → p5) ∧ p3) ∨ p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37809159475588737392655933154 : ((((p2 ∧ (p1 ∧ ((False ∧ p5) ∨ (((p3 ∧ ((p1 ∨ p2) ∧ p2)) → (False ∨ ((p4 → (p4 ∧ p5)) ∧ p1))) → p4)))) → p4) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114550309817415389711499053413 : (((((((p2 ∧ p2) ∧ (p2 ∨ ((p3 ∧ False) → (True ∨ p1)))) ∨ p3) ∧ False) ∨ False) ∧ ((p2 ∨ (p3 → p4)) → (False → p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88046947973971475529791787721 : (((((p4 ∨ p3) ∨ p2) ∨ True) ∧ (((p1 ∨ ((p4 → p3) ∧ p4)) → ((((p2 ∨ p3) ∨ p5) → False) ∨ (p5 → (p4 ∨ p5)))) → p5)) → p5) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : ((p1 ∨ ((p4 → p3) ∧ p4)) → ((((p2 ∨ p3) ∨ p5) → False) ∨ (p5 → (p4 ∨ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h7
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : ((p1 ∨ ((p4 → p3) ∧ p4)) → ((((p2 ∨ p3) ∨ p5) → False) ∨ (p5 → (p4 ∨ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h17
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h27 : ((p1 ∨ ((p4 → p3) ∧ p4)) → ((((p2 ∨ p3) ∨ p5) → False) ∨ (p5 → (p4 ∨ p5)))) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h34
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h35 := h3 h27
      -- One of the premise coincides with the conclusion.
      exact h35
  case inr h36 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h37 : ((p1 ∨ ((p4 → p3) ∧ p4)) → ((((p2 ∨ p3) ∨ p5) → False) ∨ (p5 → (p4 ∨ p5)))) := by
      -- Implications on the right can always be decomposed.
      intro h38
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h44
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h45 := h3 h37
    -- One of the premise coincides with the conclusion.
    exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66261630802096566044013393309 : ((p5 ∨ ((p5 → (p5 ∧ (p1 ∨ p5))) → (((p4 ∧ ((p2 → True) ∨ ((p4 → p3) ∧ False))) → p3) ∨ (True ∨ ((True ∨ p3) ∧ p1))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40370789402319359052612873477 : (((((p2 ∨ ((True ∧ p3) → (p4 ∧ (p1 ∨ ((((p2 ∧ (p5 ∧ (p5 ∧ p1))) → False) ∧ (p4 ∨ p4)) ∧ p5))))) → p5) ∨ p5) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344393535579286344431437211537 : (p2 → (p4 ∨ (p4 ∨ (((p3 ∨ False) ∧ (((False ∧ ((p4 ∧ (p4 ∨ (((p1 ∧ p4) → p3) → False))) ∧ p4)) ∧ (p4 → True)) ∧ p2)) ∨ True)))) := by
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
theorem thm_5_vars_157982106294930084484307305539 : (((((p4 ∧ ((p1 ∨ p2) ∧ p5)) ∧ p4) ∨ p4) → (p4 → ((p1 ∨ False) → (p4 → (p3 ∨ p3))))) ∨ (((p5 → True) ∨ (p5 → p5)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112590347417511138371943971556 : (((((p4 ∨ (((p1 ∧ p1) ∧ p4) → ((False ∨ (False ∧ p2)) ∨ p1))) → ((p1 ∨ (p4 ∧ False)) ∧ p5)) ∧ (p5 → p2)) → p1) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (((p1 ∧ p1) ∧ p4) → ((False ∨ (False ∧ p2)) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45077994303529181859300114882 : ((((p1 ∧ p1) → ((p4 ∧ (((((p4 ∧ p2) ∧ p2) ∨ (True ∧ p5)) → (p2 ∨ p4)) ∨ ((p4 ∨ False) ∧ p1))) ∧ (False → p1))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137900356212198341541252506678 : ((p4 ∨ ((p3 ∨ ((True → ((p3 ∧ p4) ∧ (p5 → False))) ∨ (p1 ∨ ((False → p2) ∨ True)))) ∨ (p2 ∧ (p5 ∧ False)))) ∨ ((p1 → p4) → False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117824792300464520156267156572 : ((p4 ∧ (p2 ∧ (False ∨ ((p1 → ((p4 ∨ (True ∧ ((False ∨ True) ∨ ((p2 → p4) ∧ (True ∨ (p3 ∨ p2)))))) → p1)) → p1)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180412467911813238861112645042 : (((p5 → (p5 ∧ (((p3 ∨ p4) → (p5 → p5)) → p3))) ∨ (p1 ∧ False)) → (True ∧ ((True ∧ ((p3 ∨ p2) ∨ (p1 → p5))) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173155281956361324210225519851 : ((p3 ∨ ((False → p2) → ((p5 ∨ p4) ∨ ((((True ∧ p3) ∧ p4) ∨ p5) ∧ False)))) ∨ (True → (True ∨ (p4 ∧ (p1 ∧ (False ∨ (p5 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876883483804161245485630948139 : (((((p2 → ((False → (p2 ∨ False)) ∧ (((p5 → False) ∧ True) ∧ (p1 ∧ True)))) ∧ (True → (((p1 ∨ p3) ∨ False) → p3))) ∧ (p2 ∨ p1)) → p3) ∧ True) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 ∨ p3) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : ((p1 ∨ p3) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- One of the premise coincides with the conclusion.
    exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233320518312071272853678422521 : ((True ∨ (True → p5)) → ((((True → (False ∨ ((p2 → True) ∧ True))) ∧ ((p4 ∨ (p4 ∧ p4)) → True)) ∧ False) ∨ (p3 ∨ (p5 → (p2 → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731877470995197792129026641913 : ((((p4 → (p3 → False)) → ((p5 ∧ (p1 → ((p4 ∨ p3) ∧ False))) ∧ ((p4 ∨ (p4 → (False → p1))) ∧ (p2 ∨ ((p3 → False) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156918629088065372417965606094 : (((((p3 ∨ (False ∨ p5)) ∨ ((p5 ∨ ((p3 ∨ p1) ∧ p3)) ∧ ((False ∧ False) → p5))) → p1) ∨ p2) ∨ (p5 → (p4 → (p4 → (p3 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226493671996020145170348097924 : (((p2 → p3) ∨ p4) ∨ (p1 → ((False → p2) → ((p1 ∧ False) ∨ (((p2 ∨ p5) → ((p5 ∧ ((False → (p1 ∨ p5)) → p2)) ∧ p2)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_217343640802271316066262029644 : (((p1 ∨ (p5 → p2)) ∨ p2) → ((((((((False ∨ p3) ∧ (p3 ∨ p4)) → False) → False) → p5) ∧ (((False ∧ p3) ∨ True) → False)) → p3) ∨ p2)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((False ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((False ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38729999470036697742928872290 : (((((True → p4) → (p4 ∧ (p5 ∧ p5))) → ((p1 → (p1 ∧ True)) ∧ ((p5 → p4) → (((True → False) → (False → True)) → p1)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45790344658027613341321269611 : (((p1 → ((p1 ∨ ((((p3 ∧ (((p2 ∨ p3) ∨ p1) ∨ p5)) ∨ (True ∧ p5)) ∨ ((p5 → p5) ∨ p4)) ∨ p3)) → (p3 ∨ False))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654307000889731026665723830235 : (((((((((((p5 → (False → p2)) ∧ p5) → p5) → False) ∨ (False ∨ (p2 ∧ p5))) ∧ p3) ∨ ((p1 ∨ p3) ∧ p2)) ∨ p3) ∨ (False → False)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_679091236826891817283943550732 : ((((p2 ∨ (((((True ∧ ((False → False) → (p2 ∨ p5))) ∨ (False → (p2 ∨ False))) → False) ∧ p4) ∧ p3)) ∨ ((p3 ∨ True) ∨ (p2 ∧ p3))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56657601003469761618170255646 : ((((p4 ∨ p2) ∧ p4) ∧ (p3 ∧ ((p2 ∨ p3) → ((((p3 → (p1 ∨ (p3 ∨ (True → p5)))) ∨ (p2 ∧ p2)) ∨ (p4 → False)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232747745573228335804808414428 : ((p1 ∧ (p3 → True)) → (((p4 ∨ ((p1 ∧ ((True ∧ (p5 ∨ (p4 → p2))) ∨ ((p5 → p1) ∨ p1))) ∨ False)) → False) → (p3 ∧ (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ ((p1 ∧ ((True ∧ (p5 ∨ (p4 → p2))) ∨ ((p5 → p1) ∨ p1))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ ((p1 ∧ ((True ∧ (p5 ∨ (p4 → p2))) ∨ ((p5 → p1) ∨ p1))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : (p4 ∨ ((p1 ∧ ((True ∧ (p5 ∨ (p4 → p2))) ∨ ((p5 → p1) ∨ p1))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748367497754235209139002964012 : ((((p2 → p2) → ((p1 → p5) → ((p1 ∨ ((((p4 ∨ p4) → p1) ∨ (p1 ∨ p2)) ∧ p3)) ∧ ((p2 ∧ (p2 ∧ (True → p3))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48838894900097427969007318147 : (((False ∨ ((False ∨ False) ∧ (((False ∨ True) → (p3 ∨ p5)) ∨ ((((p3 → p4) ∧ p5) ∨ p5) → (p1 ∧ p2))))) ∧ ((p3 → p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67811968967680996868882247378 : ((p2 → (((p2 ∧ False) ∨ ((p3 → p4) ∧ ((p2 ∧ (((p2 → (p3 ∨ ((True ∨ (p4 ∧ True)) → True))) ∧ p4) ∨ False)) → p3))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135783906816434017725004947749 : ((((p4 ∧ (((p4 ∧ True) ∨ (p4 ∨ (True ∨ p2))) ∧ p5)) → (p2 → p2)) → (((p3 → (p5 ∨ p5)) → p4) ∨ p2)) ∨ (True ∨ (False ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593791108235980584056649627098 : (((((p1 ∨ (True ∧ (p3 ∨ ((p1 ∧ True) ∧ ((p1 ∧ p5) ∨ ((True → p3) ∨ (p1 → p5))))))) ∧ (((False ∧ p1) → p1) → p4)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773368383582156573266119523396 : (((False ∨ ((p3 ∨ (((p3 ∧ ((((False → True) → True) → ((p4 ∧ True) → p3)) ∧ p3)) ∧ (p1 ∨ (p3 → (p4 ∨ True)))) ∧ p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41844355251933939881934090160 : ((((p5 ∨ (p1 ∨ p5)) ∧ ((p2 ∧ (True → (((((((False ∨ p1) ∨ p5) → p5) ∨ p1) ∧ p4) → (p3 ∨ p3)) ∨ False))) ∨ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161195199384084975480473046315 : (((p4 ∨ p3) ∨ (p5 ∧ ((p3 ∧ ((True ∧ ((p2 ∨ p5) → p2)) ∨ (p1 ∨ p5))) ∧ (p4 ∨ p5)))) → (False ∨ ((False → False) ∧ (p5 → True)))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
          -- Implications on the right can always be decomposed.
          intro h32
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h35
          -- False on the left can always be used.
          apply False.elim h35
          -- Implications on the right can always be decomposed.
          intro h36
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h38
          -- False on the left can always be used.
          apply False.elim h38
          -- Implications on the right can always be decomposed.
          intro h39
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190958387376949332422012078973 : (((p3 ∨ ((p4 ∨ True) ∧ True)) ∧ ((p4 ∨ p3) ∧ p1)) ∨ (False → (False → (((p3 ∨ (True → p2)) → False) → (((p3 → p1) → False) ∨ p1))))) := by
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
theorem thm_5_vars_262437771148536570398341835081 : (True ∧ ((p5 ∧ ((((p3 ∨ (p1 → (p5 ∧ p1))) ∨ (False → p5)) → ((((True → p3) ∧ (True ∧ p5)) → p5) ∧ (False ∧ p3))) ∧ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147547004532332128709945522848 : (((p4 → ((((((True ∧ p3) ∨ (False ∨ ((p5 → (True ∧ False)) ∧ p3))) → False) → p5) → p2) → False)) ∨ True) ∨ (p5 → (True ∧ (p5 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326831171337180530959506727488 : (True → ((((True ∧ (p1 ∧ (p5 ∧ (p5 ∨ ((p2 ∨ ((False ∨ ((True ∧ p2) ∧ (p3 ∨ p2))) ∧ True)) ∨ True))))) ∧ (p4 ∨ True)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137643568453205842153460362230 : ((False ∨ (((((True → False) ∧ p2) ∧ (p3 → p1)) ∧ p2) ∨ ((p3 ∧ (False ∧ p3)) ∨ (p2 ∨ ((p2 → False) ∨ True))))) ∨ ((False → p4) ∧ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304125788750319570832551805061 : (p1 ∨ ((p5 → (((p2 → (((True ∨ p5) → ((p5 ∧ p1) → p4)) → p4)) ∨ (False ∨ (p2 ∨ (p2 ∧ False)))) ∨ ((p4 ∧ p4) ∨ p5))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191499123097126997338089341353 : ((False ∧ (((p5 ∨ (p3 → (False ∨ True))) ∧ p5) ∧ p5)) ∨ (((True ∧ ((False ∨ p3) ∨ (False ∧ (False → (p1 ∧ True))))) ∧ p3) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254165473279702988206061200152 : ((p2 ∧ p1) → ((((((p2 → False) ∧ (((p1 ∨ p1) ∨ (False ∨ p5)) ∧ (p3 ∨ p1))) → p5) ∧ p2) ∨ True) ∧ ((True ∧ (p4 ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233337097469848175169915569202 : ((True ∨ (p2 → p5)) → ((((p1 ∧ p3) ∨ (p5 → False)) → (p3 ∨ ((p5 ∧ (p2 → True)) → (((p5 → p3) ∨ (p4 ∧ p5)) ∨ p5)))) ∧ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804373052260547674475038297256 : (((p3 → ((False → (((True ∧ ((False → (p3 ∧ p5)) ∧ p1)) ∧ p3) ∨ True)) → ((((p1 ∨ p3) ∧ (True → (p5 → True))) ∧ p5) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312091093642972562723474606399 : (p2 ∨ (p5 ∨ (p1 ∨ (p2 ∨ ((p2 ∨ True) ∨ (p5 ∨ ((p5 ∨ (False → p1)) ∧ ((((p5 → p5) → (p5 ∨ p3)) → (p1 ∨ p5)) → False)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69993592779223209326450075808 : (((((((p5 → (True ∧ (p4 → p2))) ∧ (((p4 ∧ p5) → (p2 ∧ p2)) → (p5 ∨ p4))) ∧ (True ∧ (p3 ∧ p5))) ∨ True) → False) ∧ p1) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 → (True ∧ (p4 → p2))) ∧ (((p4 ∧ p5) → (p2 ∧ p2)) → (p5 ∨ p4))) ∧ (True ∧ (p3 ∧ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263571220427786440654022451125 : (True ∧ (((p4 ∧ (((p5 ∨ p3) ∧ p5) ∧ p3)) ∨ (((True ∨ (True ∨ (False → (True → False)))) ∧ True) ∧ True)) ∨ ((p5 ∧ p1) ∨ (p4 ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652368621526736376006788890273 : ((((p4 ∧ (((True ∧ p3) ∨ ((False → p5) ∧ p3)) ∧ (False ∨ ((((p3 → ((False → p2) ∧ p4)) ∨ p4) ∧ False) ∧ p2)))) ∧ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106339582185675891311367082912 : (((False ∧ (((p3 ∨ False) → p4) ∧ ((False ∨ p2) ∧ p5))) ∨ (((((p5 ∧ True) ∧ (p5 ∧ p3)) ∧ p4) ∨ (False → p4)) ∨ p1)) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219872191936355714696699120012 : ((p3 → (p1 → (p1 → p4))) → ((p4 ∧ (((p1 → p1) ∧ ((True ∧ ((False ∨ True) ∧ True)) → p4)) ∧ (False → ((p1 ∨ True) → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



