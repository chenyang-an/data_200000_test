variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191306771785112961850758767647 : (((p3 → p4) ∧ (((p5 → True) → p3) ∧ (p2 ∨ False))) ∨ (p2 → (((p5 ∨ p2) ∧ False) → ((p5 → (False → p5)) → (p2 ∧ (p5 ∧ p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214566949558683140855287951942 : (((p2 ∨ True) ∧ (p4 ∧ p2)) ∨ (((p4 ∧ p2) ∨ (False ∨ True)) ∨ (((p1 ∧ (p4 → p5)) ∨ ((False ∨ p4) → (p4 → True))) ∨ (p3 → p2)))) := by
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
theorem thm_5_vars_56297818746588924284767302387 : (((((p2 → p3) ∨ False) ∧ True) → ((((True ∧ ((p3 ∨ p5) ∨ p4)) ∧ p1) → False) ∨ ((p1 ∨ True) ∨ (p4 → (True ∨ (True ∨ p1)))))) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354782239103689200199862566498 : (p5 → (((p2 → ((p2 → (False ∧ p1)) ∨ (p4 → p5))) ∧ (((p2 ∧ True) ∧ (p5 → (False ∧ True))) ∧ (((p5 → p4) ∧ p1) → p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38581181280304607198689284675 : ((((((((p5 ∧ True) ∨ p2) ∧ p2) → (p1 → True)) → p4) → ((((False ∧ ((True ∧ True) ∨ True)) ∨ p3) ∧ False) ∨ (False ∧ p1))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53414414272463237542826260518 : (((((False → p1) ∧ (p2 → (p3 ∧ p2))) ∧ (p3 → (p2 ∧ p5))) → ((p3 ∨ True) ∨ ((((False ∧ True) → False) → (p1 ∧ p5)) ∨ p2))) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2202406542281515673447652312 : ((p3 ∨ (((p5 → (p2 ∧ p5)) ∧ p5) ∨ (((p4 → (p4 → False)) ∨ p4) → p2))) ∨ (((p1 ∨ ((p5 ∧ p2) → True)) ∨ False) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754614992383530016545476216729 : (((False ∧ (p3 ∧ (((((p5 → False) ∧ (p5 ∧ p2)) ∨ (p3 ∨ False)) ∨ ((((p4 → p1) ∨ p4) ∨ (p4 ∨ True)) ∧ (p4 → p5))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316457233242982058251390639049 : (p3 ∨ (p1 ∨ (((p4 → p4) → p5) ∨ ((((((p2 ∧ p2) ∧ p1) ∨ False) ∨ False) ∧ p5) ∨ ((p4 ∨ ((p2 ∨ p1) ∨ p2)) → (p4 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59822915795209917193759281240 : (((p3 ∧ p1) → ((((p1 → p3) → (p4 → p3)) → (p4 ∧ ((((True → True) → False) ∨ ((p3 → (True ∨ p4)) ∨ p1)) → p2))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231673180826372986618559014757 : (((p1 ∧ False) → p5) → ((p5 ∨ True) → (((p3 → ((p4 ∧ (p1 ∨ True)) ∨ (p1 → p2))) ∧ (p5 ∧ (p3 ∨ ((p2 ∧ p1) ∧ p1)))) → p5))) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198189387191478592058464161847 : (((False → p1) → ((True → (p1 → p3)) ∧ p2)) ∨ ((p1 → (((((p4 ∧ ((False ∨ p3) → False)) ∨ p1) ∨ (p4 ∨ p4)) ∨ p2) ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118158251616176620018314899838 : ((False ∨ ((p2 → (False ∧ (p4 ∧ p1))) → (((True ∨ (True ∧ ((False ∨ ((p1 ∧ p4) ∧ p2)) ∧ p2))) ∧ (p3 ∨ True)) ∧ p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148016492938597123488376466740 : ((((((True → ((False ∨ p2) ∧ p3)) ∨ (p4 ∧ p4)) ∧ p1) ∨ (((p4 ∨ p5) ∧ p3) ∨ True)) ∨ (True → p1)) ∨ (((p1 ∨ p5) ∨ False) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179921860268721154594729929360 : (((((((((p3 ∨ p5) → p1) → p2) ∧ p1) → p4) ∨ p1) → p2) ∨ False) → ((((p3 → p2) ∨ p2) → p5) → ((True ∧ p1) → (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((((((p3 ∨ p5) → p1) → p2) ∧ p1) → p4) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117688414765801431962782994460 : ((p3 ∧ (((p2 ∧ p1) → False) ∨ ((p3 ∧ p3) ∧ ((p1 → (((p4 → (p5 ∨ False)) ∧ (p2 ∧ False)) ∧ (p1 ∧ p5))) ∨ p4)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734533301067150749160812446729 : ((((p1 ∨ p1) ∧ (((p5 ∨ True) → (((p2 → True) ∨ (p1 ∧ ((True → ((True ∨ p3) ∧ True)) ∨ (p3 → (p5 ∧ True))))) ∨ True)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252766412634259090918886333141 : ((True ∧ True) → ((((True ∨ p4) ∨ (p1 → (p5 ∧ (False ∨ False)))) → ((p5 ∨ (((p3 ∨ p3) → False) ∨ p1)) ∨ True)) ∧ (p3 → (p3 ∧ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226299998806567873197565010907 : (((p4 ∨ p4) ∨ p1) ∨ (p1 ∨ ((True → ((p2 ∧ p3) → (((p5 ∨ True) → p4) → p2))) → (p5 ∨ (((p3 ∨ True) → True) ∨ (False ∨ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68715917726586580803125239071 : ((p4 → ((((p3 ∧ ((True ∧ p1) ∨ (p4 → p5))) → (((p2 ∨ ((False ∨ p3) → p1)) ∧ False) ∨ p4)) → p1) ∨ ((p1 ∨ p4) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47142490613423009227887662141 : ((((p1 → (True ∧ ((p2 ∨ ((p2 → p4) ∧ (p3 ∨ (True ∧ (p2 ∨ p1))))) ∧ False))) ∧ ((p4 ∧ (p4 ∧ p2)) ∧ p4)) ∨ (p4 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689916827020041851567167836943 : (((((True → p4) → ((p1 ∧ p5) ∨ (((False → (p1 → (p1 ∧ p3))) → p1) ∨ p1))) ∨ (p3 → ((p3 ∧ p2) ∨ ((p4 → p4) ∨ False)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192077009175298533477700379499 : ((p3 → (p1 ∨ (((p1 ∧ p5) ∧ p1) ∧ (p5 ∨ p1)))) ∨ (True ∨ ((((p2 ∨ p3) → p1) ∧ (p4 ∨ (p2 ∧ ((p3 ∨ p3) ∨ p4)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39755847540327446654771365980 : (((True → (((p2 ∧ p4) ∧ (((p2 → ((((p4 → p3) → True) ∨ p2) ∧ ((p2 ∨ p1) ∨ True))) → (p5 ∧ p2)) → p5)) → p1)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57349965162984480449414131138 : (((p3 ∧ (True ∧ True)) ∨ ((p3 ∧ (((p1 → (True ∨ p2)) → p2) → ((p1 ∨ p5) ∨ ((p1 ∨ p1) → p2)))) ∨ (p5 → (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60111118074011544800054847178 : (((p3 ∨ p3) → ((p4 ∧ (((((p1 ∨ ((p5 ∨ False) ∧ ((p1 → p1) → True))) ∧ p3) → p4) → p3) ∨ p2)) → ((p2 ∧ p5) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956936501891408741510367745724 : ((((True ∧ (p2 → True)) → ((((False → p2) ∧ True) ∨ ((p1 → p4) → (p1 ∧ (p4 → ((p2 ∨ (p1 ∨ (p5 → p1))) ∧ True))))) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (p2 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746668135417319907338395849 : (((p3 ∨ (True ∧ True)) ∧ (((p3 → ((((True ∨ (True ∧ False)) ∨ p1) ∨ p3) ∨ (p2 ∨ (p4 ∨ (p1 → p4))))) → True) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631399019958705980407373590601 : (((((((((True → p1) ∧ ((p2 → p2) ∨ (((False ∧ (p3 → (p3 ∧ p1))) ∨ p3) ∧ p5))) ∧ p2) ∨ p5) ∨ (p1 → False)) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598474774480834224104564183464 : ((((((False ∨ p1) ∨ p2) → ((False ∨ (p5 → (p4 ∨ p5))) ∧ ((((p1 → p1) ∧ (p5 → (False ∨ p3))) ∧ (True ∨ p3)) → True))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158368651475779760326107977369 : (((p3 ∨ p3) ∧ (p2 ∧ (((((p2 → p1) → (((p3 ∧ p1) ∨ p2) ∧ p3)) ∨ p1) ∨ p1) → True))) ∨ ((p4 ∨ (p4 → (True ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37639258006947807574536221326 : ((((((p4 ∧ p2) ∧ ((True → p5) ∧ ((p5 ∧ (p2 → False)) → ((p5 ∨ ((False ∧ p5) ∨ (p3 ∨ True))) → True)))) ∨ p5) → p5) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1962573901745412433951354971 : ((((p3 ∨ False) ∧ (False ∧ p5)) ∨ (((p1 → True) → True) ∧ (p5 → ((True → (p4 ∨ p1)) ∨ True)))) ∨ ((p1 ∨ p1) ∨ (p3 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62940681127021301203762490524 : ((p4 ∧ (p4 ∧ (((((((False ∧ False) ∨ ((((True ∧ False) ∧ p4) → p3) ∨ (False → False))) ∧ p1) ∧ p5) ∨ (p5 ∧ p2)) ∧ True) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241568593203944566920722566904 : ((False → p3) ∧ (p4 → (((((False → True) ∨ ((((((True → p5) → p2) → (p1 ∨ p3)) ∨ p3) ∧ p3) ∧ p2)) → p1) ∧ (True ∨ True)) ∨ True))) := by
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
theorem thm_5_vars_323937419952895275036814713553 : (p5 ∨ (((True ∧ True) ∨ ((((p2 → p3) ∨ (p5 ∨ (False ∨ (p1 → p2)))) ∨ p5) → False)) → ((p2 ∧ p1) ∨ (((p3 ∨ p2) ∨ True) ∨ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50170665785735352785563683867 : ((((((p1 ∧ False) ∨ (((p4 → True) → (p1 ∨ p2)) ∨ (False ∧ ((p4 ∨ p4) ∧ False)))) ∧ p5) ∧ p2) ∨ ((p3 → (True ∧ True)) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782026038398365905718488166826 : (((p2 ∨ (p5 → (((((True ∨ (((True ∨ (p5 ∧ (p1 → p4))) → True) ∨ p5)) ∨ (False ∧ False)) → p2) ∧ (False → (p1 ∨ p5))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46374543415158567133381832079 : (((((p1 ∧ p2) → (p2 → ((((p4 → False) ∨ p5) → p3) ∨ True))) → ((False ∨ ((True → (False → p5)) → p4)) → p4)) ∧ (p2 → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    have h5 : (True → (False → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213798518907730483051965431491 : (((p2 ∧ (p5 ∧ p3)) ∨ p1) ∨ (((((True → (p1 ∧ p1)) ∧ True) ∨ p5) ∧ (p1 → (p4 ∧ (p5 ∨ (False ∨ p4))))) ∨ ((p3 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677660818833225461507647899833 : ((((((p4 ∧ ((p3 → (((p2 ∧ (p4 → True)) ∧ p1) ∨ p4)) ∧ (p4 → p1))) → (p5 ∨ p3)) → p5) ∨ ((False ∨ p2) ∧ (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54402069775702181297566840568 : (((((True ∨ (p5 ∧ p1)) ∨ (p1 → p1)) ∧ p4) ∨ ((((p3 ∧ p4) ∨ (p3 ∨ p2)) ∧ (True ∨ p3)) ∨ (((p2 → p2) ∧ p2) → p2))) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357251897474792250369119677117 : (p5 → ((False ∧ p1) ∨ ((p4 ∧ p1) ∨ ((p4 ∨ (((p5 → (p1 → p2)) → p5) ∨ True)) ∨ (((p4 ∧ (p3 → p5)) ∧ (p1 ∨ False)) ∨ p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226554404258884575125289066623 : (((p4 → False) ∨ p3) ∨ (((p5 → ((p5 ∨ True) ∧ p3)) ∧ p1) ∨ ((((p5 ∧ p5) ∨ p2) → (False ∧ (False ∧ p3))) ∨ ((False → p3) ∨ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117219959481801374427763640960 : ((True ∧ ((p5 ∧ p2) ∧ ((p3 ∨ p3) ∧ (((((False ∨ p3) ∨ False) ∨ False) ∧ p4) → (p5 ∨ (((p1 → True) ∧ False) → p4)))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328117997021041916330205046249 : (True → (((((p5 ∨ p4) ∧ ((p5 ∧ (False ∧ ((p1 ∨ p4) → p3))) ∧ p5)) ∨ True) ∨ ((p5 ∧ p3) ∨ (False → False))) ∨ ((False ∨ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303705626867463802697680447896 : (p1 ∨ ((((((False ∨ ((p2 ∧ p3) ∧ (((p5 → ((p1 → p2) → p1)) ∨ p3) → p4))) → p2) → (p5 → (p3 ∧ p2))) ∧ False) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317881308167030329004953018209 : (p4 ∨ ((True ∧ ((p3 ∨ ((p4 ∨ ((False ∧ (p1 → (False ∨ True))) → p4)) ∧ (((p4 → (p4 ∨ p3)) → p5) ∨ (True ∧ p4)))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329102760714981135515132643157 : (True → ((((p4 ∨ True) ∧ p4) ∨ p4) ∨ ((((False → p4) ∧ (((((False ∧ (p1 ∨ p3)) → p2) ∧ p4) ∧ True) ∨ (p2 ∧ p2))) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48784270301405489168279695755 : ((((p4 → p3) → ((p4 → p2) → (True → (p5 ∧ (p3 ∧ ((((p4 ∧ False) ∧ True) ∨ False) ∧ (p2 ∧ False))))))) ∧ (p5 ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564416686958801649903298631263 : (((p5 ∨ (p5 → ((((((True ∧ p4) ∨ p1) ∧ (((((p2 ∨ p3) ∧ True) ∨ p5) ∧ p3) ∧ p3)) ∧ p5) ∨ (p4 ∨ (p3 → p5))) ∧ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215549066486581458368522852340 : ((p5 ∧ ((p2 ∧ True) ∧ p4)) ∨ (((True ∧ (((False → (False ∧ p2)) ∧ True) ∨ p2)) ∧ False) ∨ ((p3 ∨ False) → ((True ∧ p4) ∨ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184477363402000432486223634546 : ((((p2 ∧ ((p1 → (p2 ∧ p5)) ∧ p5)) ∨ p4) ∨ (p4 → False)) ∨ (((p4 → p5) → (((p3 → p1) ∨ p1) → (False ∨ (False → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695138459639777643704093455786 : ((((((p1 ∨ ((p2 ∨ (p3 ∨ False)) ∧ p3)) ∧ (True ∨ (True ∨ True))) ∨ p1) → (p5 ∨ (((p1 ∨ p4) ∨ (p4 ∨ True)) ∨ (p5 → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h14 =>
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
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
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
          case inr h17 =>
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
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h20 =>
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
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
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
            case inr h23 =>
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
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252799855334346600359664454924 : ((True ∧ True) → (True → (((False → p1) → (((False ∧ False) ∨ p4) ∧ ((False ∧ p1) ∨ True))) ∨ ((p4 → False) → (((p4 ∧ p4) → p5) ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215938646030916531953107833491 : ((p3 ∨ (p2 → (p1 ∨ p5))) ∨ (((True → (p1 ∧ True)) ∨ (False → ((p1 ∨ (((p4 → p4) → p5) ∧ p3)) ∨ p1))) → (p3 ∨ (False → p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234334320933984748581688259872 : ((p1 → (p5 ∧ False)) → ((((p3 ∧ p3) ∧ (p3 ∨ (False ∧ (True ∨ p1)))) ∨ ((p2 ∧ True) → p3)) → ((p5 → False) ∨ (p3 ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319559112259477896617429489864 : (p4 ∨ ((p3 ∨ ((((p1 ∧ (p1 ∨ p1)) ∧ p5) ∧ p3) ∨ True)) ∨ ((p5 ∧ ((True ∧ True) ∧ (p1 ∨ (p1 ∧ True)))) ∧ ((p3 → False) ∨ p5)))) := by
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
theorem thm_5_vars_559432483270298823995515340789 : (((p4 ∨ (((False ∨ ((((p5 → p5) ∨ p4) ∨ ((((p1 ∧ p3) ∨ (False ∨ False)) ∨ p4) ∨ p1)) → p5)) ∨ (True ∨ p5)) ∨ (p2 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305165635510675737203285091036 : (p1 ∨ ((((True → p4) ∨ (p5 ∧ ((False → p2) → ((p2 ∨ p2) ∨ (((p5 → p1) ∨ False) ∨ p2))))) → False) ∨ (False → (p1 ∧ (False ∨ p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54941873798142243823564937108 : (((((p1 ∨ True) ∨ False) ∧ (p1 → p1)) ∧ (((True ∧ (True ∧ ((p2 ∨ False) ∨ p2))) ∧ (p3 ∧ p2)) ∨ (True → ((False ∨ p2) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51956016534960976958244755081 : ((((False → ((p1 ∧ p3) ∨ p2)) ∧ ((p4 ∨ (p3 ∧ ((p1 ∧ p4) ∧ True))) ∧ p2)) ∨ ((p4 ∨ (True ∧ p4)) ∨ ((p5 ∨ False) → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356250285610881959278947141483 : (p5 → (((((p4 ∨ p4) ∧ p3) ∨ (((True ∨ p2) → (p1 ∧ False)) ∨ (p3 ∨ False))) ∨ p5) ∨ (((p4 → ((p4 ∧ p4) ∨ False)) → p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747650493994619122614018488141 : ((((True → p5) → (((((p5 → (True ∧ p1)) ∧ p3) ∨ p3) → (p2 ∧ p4)) ∨ (True → ((p4 ∨ ((p4 → p5) ∨ p1)) ∨ (False → False))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670338408572855703089003114100 : ((((((p3 ∧ p3) ∧ p4) ∨ ((((p4 → p3) ∨ (True → ((p5 → True) → ((p1 ∨ True) → p4)))) ∨ p2) ∨ p4)) ∨ ((True ∨ p1) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37557640975008360151081814923 : ((((p2 ∨ (((True ∨ (((p4 ∨ ((p2 ∧ p4) ∨ p2)) ∨ p5) ∧ (p2 ∧ ((False ∨ p2) ∨ p5)))) → p5) ∧ (p2 ∧ p2))) ∨ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739055417651519376525933750529 : ((((p3 ∧ p4) ∨ ((((p2 ∧ ((p5 → False) → (p5 ∨ (p1 ∨ False)))) ∨ True) ∨ ((p4 ∨ p2) ∧ ((p1 ∨ p5) → (p5 ∨ True)))) ∨ p2)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_64866150620362466922813684924 : ((p2 ∨ ((((True → p2) → (p1 ∨ (p2 ∧ p4))) ∨ (True ∨ ((p3 → ((p4 ∨ p1) ∧ p5)) ∨ (False → (p2 ∨ p4))))) ∨ (p1 ∧ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647691948145033374449269858994 : ((((p5 → ((False ∧ p3) → (True ∨ ((((False ∨ False) ∧ p1) → (False ∨ p3)) → (False ∨ ((p4 ∨ ((p2 ∧ p2) → p5)) → p3)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663048345264858185917089564185 : (((((p2 → (p2 ∧ True)) → (((p5 → p4) ∨ (((p4 ∧ p2) ∨ p4) → (True → (False ∧ (p4 ∨ (p3 → p5)))))) ∨ p5)) → (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38627957077499185285800479121 : (((((p1 ∧ ((p2 ∨ False) ∧ p4)) ∨ (p5 ∨ p3)) ∨ (((p5 ∧ (p5 → (p5 → (p3 ∨ p5)))) → p3) ∨ ((p4 ∨ p2) → p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263138784388588553611261854227 : (True ∧ (((p2 → (p1 ∨ p1)) ∨ ((((p2 → (p5 → (((True ∨ False) ∨ (p4 → p5)) ∧ p4))) → (p3 ∧ p4)) ∨ p5) ∧ p2)) ∨ (True ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798522423831528817577596913158 : (((p1 → (((p1 → p3) ∨ (p3 → (p2 ∧ (p1 ∧ p1)))) ∨ (False ∨ (((((p2 ∧ True) ∧ p5) ∨ p4) ∧ (p5 ∨ p1)) ∧ (p4 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206391221746856799359534440590 : ((p3 ∨ ((p1 ∧ (p5 ∧ p3)) ∨ False)) ∨ (p3 ∨ (((p3 → True) → ((True ∧ (True → (p1 ∧ True))) → p1)) ∨ ((p4 ∨ False) ∨ (p2 ∧ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324980684270939507014897099942 : (p5 ∨ ((p2 → p1) ∨ (p2 ∨ (((p3 ∨ (p4 ∧ (False ∨ True))) → (p2 → (((True ∧ (p1 ∨ p4)) ∧ p1) → (p4 ∨ False)))) ∨ (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181078381333404969056320058422 : (((p3 ∨ p5) → ((p5 ∧ (p3 ∧ (False ∧ ((False → p5) ∧ p5)))) ∧ p2)) → ((False ∧ (((False ∨ p3) ∨ (False ∨ p3)) ∧ p5)) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8112393555825272666946820358 : (((((p5 → (True ∨ True)) → ((p2 ∨ (p3 → p5)) → ((p1 → ((p1 → (p5 → False)) ∧ p1)) ∨ ((p2 ∨ p2) → p5)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_50684303979197932304034632579 : (((((False ∧ p5) ∨ (p1 ∨ p1)) → ((p3 ∧ p1) ∧ (((p2 ∨ p2) → (p3 → p1)) → (False ∨ True)))) → ((p4 ∧ p5) ∨ (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245694849383755590679424895354 : ((p3 ∧ p1) ∨ (True → (p1 → ((((True → True) → (p3 ∨ ((False ∧ p1) ∨ ((p4 ∧ p5) ∨ (p5 ∨ (p1 → (True ∨ p3))))))) ∧ False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186463696513762372628806004084 : ((((((p5 ∧ p5) → p1) ∨ (p3 → p2)) → False) ∧ (p3 ∨ p1)) → (((((p2 → (((p2 → False) → p2) ∧ True)) ∧ p2) ∧ p3) → p1) ∧ p3)) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (((p5 ∧ p5) → p1) ∨ (p3 → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h10
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : (((p5 ∧ p5) → p1) ∨ (p3 → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h22 := h14 h18
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42558900758567552353642511358 : (((p1 ∨ (p2 ∨ (((((p4 ∧ p5) ∧ p4) → ((p4 ∧ (p5 ∧ p5)) ∧ p2)) ∧ (p5 → p2)) ∨ (False ∨ (p3 → (p5 → p3)))))) ∨ p5) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601256558736924912115241026632 : ((((p2 ∧ ((((((True ∧ (p5 ∧ p1)) ∧ True) ∨ False) ∧ p1) ∨ (((p2 ∨ (p4 ∧ p2)) ∨ p4) ∧ p3)) ∧ (p1 ∧ (p1 ∨ p4)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305075872461791852394608124805 : (p1 ∨ ((((((p5 → p5) → True) ∧ p1) → p2) ∧ ((p4 → (p4 ∨ p2)) ∨ ((((p4 → p1) ∧ p1) → True) ∨ p4))) → ((True → False) ∨ True))) := by
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
theorem thm_5_vars_112012477054912464872015873321 : ((((True ∨ ((p2 ∨ True) → p4)) → ((p5 ∨ (((p3 → ((True ∨ p2) ∧ False)) → False) ∨ (p5 ∨ (p5 → p5)))) ∨ False)) ∨ p1) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646646348330170000799740532170 : ((((p1 → (p5 ∨ ((((p1 ∨ p4) ∧ p2) ∨ False) ∨ (p4 ∧ ((p3 ∧ p3) → ((((False ∨ (p4 ∧ p5)) ∧ False) → p5) → False)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217124332100170278116032994413 : ((((p4 ∨ False) ∨ p3) ∨ p1) → ((((((p2 ∨ False) → True) → p5) ∨ ((True ∧ p4) ∨ p1)) → p4) ∨ (p2 → (((p3 → True) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64017101744972848062621156763 : ((False ∨ (((p1 ∨ True) ∧ (((((True ∧ p2) ∧ p4) → ((((p2 ∧ (False ∧ p2)) ∨ p2) ∨ p4) ∨ p3)) ∧ p2) ∧ p5)) ∨ (p5 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196939675883687318183345010221 : ((((((p2 → p4) → False) ∧ p4) ∨ p3) ∨ p5) ∨ ((((p5 ∨ p1) ∨ (False → p4)) ∨ (p3 ∨ ((p4 → (p2 → True)) ∨ (p4 ∨ False)))) ∨ p2)) := by
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
theorem thm_5_vars_117506284231999613195958111709 : ((p2 ∧ ((p4 ∧ (((p4 → (False ∧ True)) ∧ (p1 → ((False ∧ p1) ∧ (p2 → p3)))) ∨ (p2 ∨ ((p5 → False) ∧ p5)))) ∧ p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199091068946521777718350150804 : ((((p2 → (p2 ∧ (p1 → p2))) → False) ∧ p1) → (p3 ∧ (((p2 ∨ ((False → False) ∧ (False ∧ (p2 ∨ p1)))) ∨ p5) ∨ (p5 ∧ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (p2 ∧ (p1 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (p2 → (p2 ∧ (p1 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h10
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700016624624457782104528402701 : (((((p4 ∧ (p3 ∧ (True ∨ True))) → ((False ∧ p1) ∧ (p1 → p1))) → (p4 ∨ (False ∧ (p4 → (False ∧ (False ∨ ((False → p1) ∨ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167476961510724339201143609806 : (((((((False ∨ p2) ∧ ((p1 ∨ (p2 ∨ p4)) ∧ p2)) ∧ p4) ∧ p3) ∧ p1) ∧ (p4 ∧ True)) → ((True ∨ p4) → (p3 → ((p5 ∧ p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h14.left
      let h18 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h6.left
        let h21 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h6.left
          let h25 := h6.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h6.left
          let h28 := h6.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h39.left
      let h43 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h31.left
        let h46 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h31.left
          let h50 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h31.left
          let h53 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749741461974250514490797251071 : (((True ∧ (((False ∧ (((True ∨ p1) → (True ∧ p1)) ∨ p3)) ∧ ((((False → (p1 ∧ p4)) ∨ (p1 ∨ p1)) → (False ∨ p5)) ∧ p3)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157145029421828711191942862744 : (((((((p4 ∨ ((p4 → (p4 ∨ p1)) ∨ (p3 ∨ True))) ∨ (True ∧ p1)) ∧ True) → p1) ∨ False) → p3) ∨ (False ∨ (((True ∨ True) ∧ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_119360717900413024357846921495 : ((p3 → (p3 ∧ ((((p4 ∧ (p5 ∧ ((((p3 ∨ False) ∨ p3) ∨ True) → (p4 → p5)))) ∨ False) → (p2 ∧ True)) → (p2 ∨ p4)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669599226259066191671532695102 : (((((p1 → ((((False ∧ False) ∧ ((p1 ∧ p2) ∧ False)) ∧ p4) ∨ ((p4 → False) ∨ p3))) ∧ (p5 ∨ (p1 ∧ p2))) ∨ ((p3 ∧ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51520036659223107726506764666 : ((((False ∨ False) ∨ ((True ∨ p2) ∨ (((p5 ∧ ((p5 ∨ p2) ∨ (p1 ∨ p5))) ∧ p4) → p5))) → (((p3 → p5) ∨ p1) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741450268213809829750929710752 : ((((p5 ∨ p1) ∨ (p4 → ((False ∧ ((p4 → p2) ∧ (p5 ∧ p2))) ∧ ((((p4 ∧ p4) ∨ p2) ∧ (p2 ∧ ((False → False) ∨ p1))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194176840761562307154145779467 : ((p2 → ((p2 ∨ (p3 ∧ p2)) ∨ (p3 ∨ (False ∧ True)))) → (((p4 → p5) ∨ ((p2 ∨ False) ∨ (p4 ∨ (p5 ∧ False)))) → ((p5 ∧ p3) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45910270278344752905492560742 : (((p4 → ((True ∨ (p4 ∨ (((p4 ∨ (((False ∧ p1) → (p3 ∧ p2)) → p4)) ∧ p2) ∨ (p3 ∨ p5)))) → (p3 ∧ (p5 → p2)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



