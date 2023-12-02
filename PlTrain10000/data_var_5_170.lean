variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9890933324244413696477227537 : (((p1 ∧ ((False ∧ ((((p3 ∨ (p1 → (p2 ∧ (p5 → p3)))) ∧ False) ∨ True) ∨ (((p2 ∨ p4) ∧ p1) → (False ∧ p1)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54962757709416436935048534422 : ((((p2 → (False ∨ p3)) ∨ (p1 → p5)) ∧ (False ∧ ((p3 ∨ (p4 → p1)) ∧ (((p1 → True) ∧ (((False ∧ p2) ∨ False) → p3)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55973520939095468699194158612 : (((((p3 ∧ p2) → p4) ∧ True) ∨ (True ∧ (p2 ∧ (((p5 → (p4 ∧ (p2 ∧ (True ∨ p2)))) ∧ p3) → (False ∧ (p3 ∧ (p2 ∧ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654590579537948803873710507837 : (((((p5 ∨ (True → (p3 ∨ (p3 → ((p2 ∧ (p2 ∧ p4)) ∨ ((((True ∧ (p3 → False)) ∨ p4) ∨ p4) ∧ True)))))) ∨ p3) ∨ (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219036322011743580269348377633 : ((p5 ∧ ((p3 ∨ p4) ∨ True)) → ((p4 ∨ (p4 ∨ ((p2 → p3) ∧ p1))) ∨ (((False → p4) ∧ False) ∨ ((p2 ∨ ((True → p4) → p1)) ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165537016695593118623979833510 : (((((True ∧ True) ∧ ((False ∨ p4) ∧ p4)) ∧ p2) ∧ (p2 ∨ ((p3 → (True ∧ p2)) ∧ False))) ∨ ((((p2 ∨ p4) ∧ p3) → p5) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39167195120134398385939406207 : ((((p5 ∨ p1) → (p3 ∨ ((p5 → ((p1 ∧ (p1 → p1)) ∨ (p3 ∧ p2))) → (((False → (False ∧ p3)) → (False → p5)) ∧ False)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211566719104560420571068859312 : (((p2 ∨ p4) → (False → True)) ∧ ((True ∧ ((True ∧ (p2 ∨ False)) ∧ (((False ∨ p3) ∧ p2) ∧ (p5 ∧ (p2 ∨ True))))) ∨ ((False → True) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32871137135281003373628599968 : ((p3 ∨ ((p1 → (((p3 ∧ ((p3 ∨ ((True ∨ True) ∨ ((p4 → False) ∧ True))) ∨ p5)) → (p3 ∧ p2)) ∧ (p4 ∨ (False ∨ False)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_233198179241489306743526163684 : ((p5 ∧ (True → False)) → ((((p2 → ((p3 ∨ (p5 ∧ p3)) ∧ (((p3 ∧ p2) ∧ (p4 ∨ p3)) ∧ p1))) → (p1 → p4)) ∧ (p5 ∧ p3)) ∨ False)) := by
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
theorem thm_5_vars_49496821471418667306090897886 : (((((False → p3) → (((((False ∧ (((p4 ∨ (p1 → p3)) → p5) ∨ False)) → p4) → p2) → p1) → False)) → p1) → (p1 ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765435412342603043590145176706 : (((p4 ∧ (((p1 → (((True ∧ p2) ∨ (p1 → (p3 ∧ p3))) → (p5 ∨ True))) → (p2 → (p3 → p5))) ∨ (p4 ∧ ((p4 ∧ False) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114946282687021207889576848846 : ((((p5 → p5) ∧ (((p4 ∨ p2) → ((True → (p5 → p2)) → p4)) ∨ p4)) → ((True → (p4 ∧ p1)) ∨ ((p2 ∧ True) → p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356023797807299869512748286342 : (p5 → ((((p3 ∨ ((((p1 → True) → p1) → p3) ∨ p2)) → ((p1 → (p1 → p1)) ∧ p5)) → (True ∧ p2)) ∨ (False → ((p3 ∨ p4) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656969478945611828783947270915 : ((((((False → (p1 ∧ p1)) → p5) → (((p4 → p2) → (False ∧ (False ∨ (p3 ∨ p5)))) ∨ ((p1 ∨ p5) ∨ (True → p3)))) ∨ (p2 ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57367741230722388899936911658 : (((p4 ∧ (p4 ∨ p5)) ∨ (((((p5 ∨ p3) ∨ (p2 ∨ p4)) ∧ (p4 → p4)) → False) ∨ ((p4 → (p2 → (False ∨ (False → False)))) ∨ p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173437044083159988439612557775 : (((((((p5 → (p2 ∨ (p2 ∨ p1))) → (True → False)) ∨ p1) ∨ False) ∧ p3) ∧ p2) → (((p1 ∧ (p4 ∨ p1)) ∨ (p1 → False)) ∧ (True → p3))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p5 → (p2 ∨ (p2 ∨ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h8
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58687027649350326359334482697 : (((p2 → p2) ∧ ((((p5 ∨ (False → p3)) → (p5 ∧ p3)) → (((p1 ∨ p5) ∧ False) ∨ (((True ∨ p5) → p5) ∨ (p2 ∨ p2)))) ∨ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p5 ∨ (False → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56398254045948963216472426587 : ((((p3 ∧ (p4 ∨ p3)) → False) → (p5 → ((((((p5 ∨ True) ∧ p1) ∧ ((p3 ∨ (True ∧ p3)) ∨ (p3 → p5))) ∨ True) → p3) → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 ∨ True) ∧ p1) ∧ ((p3 ∨ (True ∧ p3)) ∨ (p3 → p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∧ (p4 ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227845638876953524076543256835 : ((p2 ∧ (True ∨ False)) ∨ (p2 → (((p3 → p2) → ((p1 ∨ p3) ∨ ((p5 ∧ False) → True))) → (((p4 ∧ (False ∨ (p2 → p2))) → p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260283898894400611385091441421 : ((p2 → p4) → (((p3 → (p2 → p2)) ∧ (((((p3 → (p5 ∧ True)) ∨ (True → False)) ∧ True) → ((p5 ∧ (p1 ∨ p2)) ∧ p1)) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53280279256201595312666398495 : (((p3 ∧ (p4 ∧ (p2 ∨ ((p1 ∧ ((True ∨ False) → p2)) ∨ p4)))) ∨ (((p4 ∨ (p5 ∧ ((True → False) → (False → p5)))) ∨ True) ∨ p5)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117330161141355807846034751147 : ((False ∧ ((p1 ∨ ((p5 ∧ p1) ∨ p1)) ∨ ((((p5 ∨ True) ∧ (False ∨ p4)) ∨ (p2 → p3)) ∧ ((p2 → p1) ∨ (p2 → True))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234193580801200467518272930080 : ((False → (p1 ∧ False)) → ((p1 ∧ ((p2 ∧ p1) ∨ ((p2 ∧ ((((p3 ∧ (True ∨ p1)) → (False ∨ True)) ∧ p2) ∧ True)) → (True → False)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324166351496413757446350153438 : (p5 ∨ (((((p5 ∧ (p5 ∧ p1)) ∨ p2) ∨ p2) ∧ (p3 ∧ p5)) ∨ (False → (p4 ∧ (False ∨ (((p5 → True) ∧ (p1 ∧ (p1 ∨ p5))) ∧ p1)))))) := by
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
theorem thm_5_vars_179249705844985141805865603538 : ((p5 ∧ (((p1 ∨ p3) ∧ p2) ∨ (((True ∨ False) → p1) ∨ (False → True)))) ∨ (True ∨ ((p2 ∧ (False → True)) → ((p1 → p5) ∧ (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208311207658797028490083872450 : (((True → False) ∧ (False → (p1 ∨ p3))) → ((False ∧ (p3 → (((p1 ∧ (p1 → p5)) → (((p2 → (p4 ∧ True)) ∧ p5) → True)) ∧ p5))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4478134883687185273695686537 : (p2 → ((p5 → (p4 ∧ (True ∧ False))) → (p3 ∨ (((p2 ∨ p3) ∨ True) ∧ ((p1 ∨ ((p1 ∧ (p2 → False)) ∧ True)) ∨ (p2 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738817564938940124162097944602 : ((((p2 ∧ p5) ∨ ((((True → ((((p5 ∨ (False → (p5 ∨ ((p2 ∨ p5) ∨ p3)))) ∨ p2) ∨ True) → (True → False))) → p1) ∧ p2) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179366012516767327639159433905 : ((p2 ∨ ((p3 → (False → (p2 → p1))) → ((p3 ∨ p1) ∧ (p5 → p4)))) ∨ (True → (False → ((((p1 ∨ (p5 → p4)) ∨ p3) ∨ p1) ∧ p4)))) := by
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
theorem thm_5_vars_169850628965868428468545876340 : ((((((False ∧ p1) ∧ (p5 ∨ (p5 ∨ (False ∨ False)))) ∨ p2) ∨ True) ∨ (True → False)) ∧ ((p3 ∨ ((p4 → p1) ∨ (p5 ∧ p2))) → (p4 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789830310798696959819065986864 : (((p5 ∨ ((p4 ∨ (p4 → True)) ∧ (p4 ∧ (((p4 → (True → False)) ∧ ((p1 → (p5 ∨ p5)) ∧ (False ∨ False))) ∧ ((p4 ∧ p1) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174653628202455038389268765767 : ((((p3 → p4) ∨ True) ∧ ((False → False) ∧ ((((p5 ∧ p1) → p2) → p1) → p1))) → ((p2 → p5) ∨ ((p2 → p3) → (p1 ∨ (True ∧ True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142243335880517416541456248610 : ((p2 ∧ ((True ∧ (((((p5 ∨ (p4 → p4)) → p4) ∨ p4) ∧ p4) → (p4 ∨ (((False → p3) ∨ p1) → True)))) ∧ p2)) → (p3 ∨ (True ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248590091094012199962132702243 : ((p3 ∨ False) ∨ (((False → (p5 ∧ False)) → p1) → (((((p2 ∧ p2) ∧ p5) ∨ p3) ∨ True) ∨ (p2 ∨ (p2 → (p3 → (p1 ∧ (p2 → p5)))))))) := by
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
theorem thm_5_vars_241384070004818473061237839543 : ((False → False) ∧ (p1 → ((((p1 → p3) ∧ (((p5 ∨ (False → True)) ∨ ((p1 ∧ (p3 → (p2 → p4))) ∧ p4)) → True)) ∧ (p1 ∧ p2)) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62277513184781467438876892189 : ((p3 ∧ ((((True ∧ ((p4 ∧ (p3 → p4)) → (False ∨ p1))) ∧ (p1 ∧ p2)) ∧ ((p5 → (False ∧ (p1 ∧ (p2 ∨ p2)))) ∧ p1)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249629951519875986693735066643 : ((p5 ∨ p3) ∨ ((p1 → p3) → ((True ∧ ((((p4 ∧ False) ∨ p2) → (((p2 ∧ ((p5 ∧ p3) → p3)) → p5) ∧ p3)) ∨ (False → p5))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227766239068549785104068777391 : ((p1 ∧ (True → False)) ∨ ((((p5 ∧ (p3 ∧ ((False ∧ p5) → (((((p1 ∧ p4) ∨ (p3 ∧ p2)) ∨ True) ∨ True) → p5)))) ∧ p4) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55874728340576544445931761555 : (((True ∨ (p1 ∨ (p2 ∨ p2))) ∧ ((((((p4 ∧ (p4 → p2)) ∨ True) ∧ p2) ∧ (False ∧ ((True → False) ∨ p1))) ∧ False) ∨ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809408780776810564141799873796 : (((p5 → (((p1 ∧ (((p3 ∨ (False → ((((False → (p1 ∨ p2)) ∧ True) ∧ True) → p3))) ∧ ((p1 → p2) ∧ False)) → p4)) ∧ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149207425246644045395838416110 : (((True ∧ p3) ∨ ((((False ∧ p4) ∧ p4) ∨ (p1 → p3)) ∨ (p1 ∨ (p5 ∨ (p4 ∨ (False ∨ (p1 → p5))))))) ∨ ((False ∨ p3) → (True ∨ p4))) := by
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
theorem thm_5_vars_40484301712563331819584486518 : (((((p1 ∨ p1) ∨ (((p2 ∧ p2) → p1) → ((p4 ∧ (p5 ∧ ((p5 ∨ (p2 ∧ p4)) → p5))) ∨ (p1 → (p2 → p1))))) ∨ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356996490956669982779954168696 : (p5 → (((p4 ∧ False) ∧ True) ∨ ((False ∨ (p4 → p4)) → ((((p4 → p5) → ((p4 ∧ True) → (False ∨ p4))) ∨ p2) → ((True → False) → False))))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183115001628441189075819900995 : (((p5 ∨ p4) → (p5 ∨ ((p1 ∧ p3) → ((p2 ∧ p2) ∨ p1)))) ∧ (False ∨ (p1 ∨ (((p5 ∧ ((True ∧ p5) ∨ (p1 ∧ True))) → True) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245891647920436079984505401552 : ((p3 ∧ p5) ∨ ((True ∧ (p3 ∨ ((p1 → (((p3 ∨ p2) ∧ True) ∧ p1)) ∨ (((p5 ∧ True) ∨ False) → (p1 → ((True ∨ True) → True)))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314226814861570984174171323681 : (p3 ∨ (((p2 → (p5 ∧ (p3 → ((((True ∧ (p1 ∨ p3)) ∧ p4) ∧ False) ∧ ((p4 → p5) → (False ∧ False)))))) ∧ False) ∨ ((True ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260403747517683803938125065180 : ((p3 → True) → ((((p5 ∨ False) ∧ (p5 → ((p1 ∧ ((p5 ∧ (p2 ∧ (False ∧ p3))) ∨ (p3 ∨ (p1 ∨ p5)))) ∧ p2))) ∨ (False ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353656466467601346906159214877 : (p4 → (p5 ∨ ((True ∧ (p3 ∧ (p3 ∨ (((p5 ∨ p4) ∧ p5) ∨ (((p4 → ((p3 → (p2 → p4)) ∨ p3)) ∧ True) → (p3 ∨ p4)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47719981867791849818603144597 : ((((((p3 ∧ ((p1 ∧ (p1 ∧ (p4 → (p5 ∧ (p1 → (True → ((False ∧ p4) ∧ p3))))))) ∧ p2)) → False) → p1) ∨ p3) → (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343389559807324944068234387861 : (p2 → ((p1 ∧ p3) ∨ (((p5 ∧ (p5 ∧ ((p4 ∧ True) ∧ True))) ∨ ((((True ∧ p3) ∧ True) ∨ ((p5 → False) ∨ p5)) ∨ (p3 ∧ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179207325854114851027876971676 : ((p4 ∧ ((((((True ∨ p2) → (p3 ∧ p2)) ∧ p1) ∨ p4) ∧ True) ∨ p4)) ∨ (p2 ∨ ((((p5 → (p1 ∨ p4)) → p3) ∨ p5) → (p4 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58126371351700542334140190753 : (((p2 ∧ False) ∧ (((((False ∧ ((p2 → p3) → (True → p4))) → p4) ∧ (p5 ∧ p4)) → False) ∧ ((p2 → (True ∨ (True ∨ p1))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669224793519137532872835099894 : (((((p4 ∧ (((((((True → p1) → p5) ∧ p5) ∨ p2) ∨ (((p4 → p3) → False) ∨ p1)) → False) → True)) → p3) ∨ (p1 ∨ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703891169822741303674140071727 : ((((((p4 ∨ True) ∨ ((p4 → (True ∧ p5)) → p5)) ∨ False) → ((True → p1) ∧ ((p1 → ((p1 ∧ False) ∨ (p3 → (False ∧ p5)))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50543368227798488940647590687 : ((((((p3 → (p1 ∧ p3)) ∨ (p4 ∧ p4)) → (((p2 ∧ ((p1 ∨ p1) → False)) ∨ True) ∧ p3)) ∨ p3) → (p5 ∨ (True → (True ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42941115178165055001816213693 : (((p4 → (((False → p2) → (True ∨ p5)) ∧ (p1 → ((((((p4 → p1) ∧ p5) ∨ False) ∧ (True ∧ p1)) ∨ True) → (False ∨ False))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114372907302246065771609863664 : ((((p5 ∨ ((((((p3 ∧ p4) → p2) ∨ (p3 ∧ p5)) ∧ p4) ∧ (p2 ∨ p1)) ∧ p3)) ∨ p5) ∨ (False ∨ (p3 → (True → p1)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190421038601006627001123726431 : (((p2 ∨ (((p3 ∧ p1) ∨ (p1 ∧ p3)) ∨ p2)) ∨ True) ∨ ((((p5 ∨ p1) → p5) ∧ (((False → (True ∨ p5)) → p1) → (p2 ∧ False))) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949142112059209801134153727591 : (((((True → p1) ∧ p1) ∧ ((p4 ∨ (False ∧ p3)) → ((False ∧ ((((p1 → p4) ∧ p3) ∨ (False ∧ (p5 ∧ (p3 ∧ p5)))) ∨ p2)) → p2))) → p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789274393792526496255585341325 : (((p5 ∨ ((((p1 → (p2 → p4)) ∧ (p1 → (p1 ∧ False))) ∨ (p3 ∧ ((False → (p5 ∧ p4)) ∨ p3))) → (False ∧ ((False ∨ True) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725539249038010688234770701969 : (((((p1 ∧ True) ∧ p5) ∨ ((True ∧ p5) → ((((p5 ∧ p1) ∧ True) → ((p5 → p2) ∨ (p3 → (((True → p3) ∧ True) → False)))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697758329759385188315620659823 : ((((p2 → ((((p4 → p2) ∨ p1) ∧ p4) ∨ ((p1 ∧ p5) → True))) ∧ (p4 → ((p1 → (p5 ∨ p2)) ∧ (((p2 ∧ p2) ∧ p4) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724591715122141726163480797047 : ((((p1 ∨ (p1 ∨ True)) ∧ ((p3 ∧ ((False ∧ (True ∧ (False ∧ (p4 ∨ (p5 ∨ ((p3 ∨ p4) ∧ p1)))))) → (p2 ∧ (p4 ∧ p1)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158769015038031410749873285635 : ((p4 ∧ (p2 ∧ (((p3 ∨ p2) ∨ (p5 ∧ p4)) → (((p1 → False) ∧ (p1 → p3)) ∨ (p4 → p1))))) ∨ (((True → True) → (p2 ∧ p4)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698801018761994344491518747286 : (((((p2 ∨ True) → (p3 ∨ ((p1 ∧ ((True ∧ p2) → p5)) → p4))) ∨ (p1 → ((p1 → True) → (p4 → (((True ∨ p1) ∨ True) ∨ p1))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311075416876469952094497157420 : (p2 ∨ ((p2 ∨ p5) ∨ (p4 ∨ ((((p1 ∨ ((p3 ∨ p2) → False)) ∧ (p1 → p3)) ∧ (p5 ∨ False)) → ((((p3 → p1) ∨ p5) ∨ p5) ∨ False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208845384162912384390329388288 : ((p3 ∧ (p2 → (p4 ∧ (False ∧ False)))) → (p4 ∨ (p5 ∨ (p5 ∨ ((((((p3 → True) → p1) ∧ (p1 → p5)) ∧ p1) ∧ p4) → (p2 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140867887765024533385523438401 : (((((p4 ∧ p5) → (p3 ∧ (True ∨ p1))) ∧ ((p1 → p1) → p1)) → ((p5 ∨ False) ∨ (p2 ∧ ((p2 ∨ p2) ∨ False)))) → (p3 → (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112689592300425778507858801813 : (((((p2 → True) → (p4 ∧ ((((p2 ∨ p1) → (p2 ∧ p4)) ∨ p1) → (p5 → p4)))) ∧ ((False ∨ p1) ∧ (p4 → p2))) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168025061094325251316312967722 : (((False → ((p3 ∧ p1) → (p2 ∧ p4))) ∨ ((p4 ∧ (((p3 → p1) ∧ True) ∨ False)) ∨ p1)) → ((((p1 → (False ∧ p2)) → False) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338797862802413635752308535064 : (p1 → ((False ∨ False) ∨ ((False ∨ ((((((False ∧ False) ∨ (p2 ∨ p3)) ∨ p5) → (False → (True ∨ (p5 ∧ p2)))) → False) ∨ (p5 ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159863560789357094295177286021 : ((((((False → p2) ∨ ((True ∨ (p2 ∧ (p3 ∨ ((p2 ∧ p2) ∨ p3)))) ∧ p3)) ∧ p5) ∧ False) → True) → (((p2 ∨ (False ∨ p4)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249768198902415449923502036053 : ((p5 ∨ p5) ∨ (p5 → ((False → ((((p1 ∧ False) ∧ (False ∨ (p1 ∧ True))) ∨ p1) ∧ p2)) → (p4 → (True → (((p2 ∨ p1) ∨ p2) ∨ p5)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305802701430477206688719968436 : (p1 ∨ (((p2 → (False ∨ (p2 ∨ False))) ∨ (False ∨ False)) → (((p2 ∧ ((True ∧ p2) ∨ ((p2 → p3) ∧ ((False ∨ True) → p4)))) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313359777903723791336649232176 : (p3 ∨ ((p3 → ((((False ∨ ((p2 ∨ False) ∧ (False ∨ (True → (False ∨ p3))))) ∧ p1) ∧ (((p5 ∨ (p3 ∨ p3)) ∨ p4) ∨ p5)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631287773300408416549207576908 : (((((((p1 ∧ True) → (p1 ∨ ((p3 ∨ False) ∧ (((p2 → (p1 ∧ p3)) ∨ (False ∧ (p5 → (p3 ∨ p2)))) ∧ p2)))) → p1) → p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41003533716048630350510161830 : (((((((p4 ∧ ((p2 → ((p4 ∧ p5) → p1)) ∨ ((True ∨ p4) ∧ p5))) ∧ (p4 ∨ (True → True))) ∨ p3) ∧ p3) → (p1 ∨ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786573108406360815849556699949 : (((p4 ∨ (((True ∧ (True ∧ p1)) ∧ (((p4 ∧ True) ∨ p1) ∧ p4)) → ((((p4 ∧ p3) ∨ p4) ∧ (p2 ∧ p5)) ∨ ((False ∧ p5) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174295418853859266190975847180 : ((((p2 ∧ (p2 ∧ ((p1 ∧ (False ∧ p1)) ∨ False))) ∧ p4) ∨ ((p3 → p1) ∨ p3)) → (((p2 ∨ (p2 ∧ p5)) ∨ ((True ∨ p4) ∨ True)) ∨ p3)) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
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
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115995097145038362183435122102 : ((((p1 ∧ (p4 → p5)) → True) → (((p2 ∧ False) ∧ p4) ∨ (True → (True ∧ ((((p2 ∧ p1) → p4) → (False ∧ False)) → p5))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50762616624341716764803059247 : (((True ∨ ((p4 ∧ ((True ∧ False) → (p3 → (False ∨ p3)))) ∧ ((p4 ∨ (p1 ∧ (p5 ∧ p3))) ∧ True))) → (p5 ∨ ((p2 ∨ p2) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49230292618699248470261096459 : ((((p4 ∨ False) ∨ ((p1 ∧ p4) ∧ ((p2 ∨ ((p5 → ((p4 → (p4 → False)) → (False ∧ p1))) ∧ True)) ∨ False))) ∨ (p2 ∧ (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655465025865684876491318423139 : (((((p2 ∨ ((((True ∧ p1) ∨ p4) → (((((p1 ∨ p2) ∧ False) ∧ (p5 ∧ p1)) → p4) → p5)) → p1)) ∨ (True ∨ p4)) ∨ (False ∧ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54353109741003854275714083403 : (((p2 ∨ ((p4 ∧ (p4 ∨ p2)) → (p4 → p3))) ∧ ((False ∧ ((((p4 ∨ True) ∨ (False ∨ (False ∧ p5))) ∨ (p4 → p4)) → p2)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640898644233402930980437174461 : (((((p5 → p3) ∧ ((((p1 ∧ p4) ∨ ((p4 ∧ (p1 → p4)) ∨ (p5 → p3))) ∨ ((p3 ∨ p3) ∧ ((p4 ∨ p2) ∨ True))) ∧ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126794046669091059915968217520 : ((p5 ∧ (((p2 ∧ ((False ∨ True) → (True ∨ (True ∨ ((p5 ∧ False) ∧ (((False → p4) → p5) → False)))))) → (p5 ∨ p2)) ∨ p4)) → (p4 → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165693655555928968726020095223 : (((p5 ∧ (p1 ∧ (p3 ∨ (p5 ∨ p1)))) → (p4 → ((p3 → (p2 ∨ p5)) → (p3 ∧ p3)))) ∨ (p1 ∨ (((p4 ∧ (p5 ∧ True)) → True) ∨ p1))) := by
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
theorem thm_5_vars_763591492873500821710832664159 : (((p3 ∧ (p4 ∧ (((False ∨ p2) ∨ (True → (p3 ∧ ((p2 ∨ (p3 ∨ p1)) → p3)))) → (((p4 ∨ p5) ∨ (False ∨ False)) ∨ (p4 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215728800005966805748629056831 : ((False ∨ (p2 ∨ (p3 ∧ True))) ∨ (((p2 → ((p5 ∧ p5) → ((p2 → (p2 ∨ (p2 ∧ (p1 ∧ (False → False))))) → p2))) → (True ∧ False)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p5 ∧ p5) → ((p2 → (p2 ∨ (p2 ∧ (p1 ∧ (False → False))))) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59388006729590798143095292690 : (((True → False) ∨ (p5 ∧ (((p4 ∧ ((True ∨ p1) → (False ∧ ((p3 ∨ p5) ∧ (True ∨ p5))))) ∨ (True ∧ True)) ∧ (False ∨ (p3 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43671309872671434154752090932 : (((((p3 → (((False → p2) ∨ (True ∧ True)) ∧ ((p5 ∧ p1) ∨ (False ∧ p1)))) ∧ (p1 ∧ (((p1 ∧ p3) → True) ∧ p3))) → p4) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890735295269133479609984672531 : ((((False ∨ (p3 → ((((p1 → False) ∨ (p1 → p5)) ∨ p3) ∧ (p5 → (((p4 ∧ p4) ∧ (False → p4)) ∨ (p4 ∨ True)))))) → (False ∨ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p3 → ((((p1 → False) ∨ (p1 → p5)) ∨ p3) ∧ (p5 → (((p4 ∧ p4) ∧ (False → p4)) ∨ (p4 ∨ True)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744925030526928969090005747625 : ((((p4 ∧ True) → ((p2 ∧ ((p2 → (((p3 ∨ (False ∧ p3)) → (False ∨ (p5 ∨ (p2 ∧ True)))) → p3)) ∨ (p2 → (p5 ∨ p5)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307365038686611904347400661667 : (p1 ∨ (p4 ∨ (((p3 → p1) ∨ ((True ∧ ((((p2 → (p5 → False)) → p2) ∨ False) ∧ False)) ∨ (p5 ∨ ((True → (True → True)) ∨ p1)))) ∨ False))) := by
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
theorem thm_5_vars_158313863490578800902920952597 : (((p1 ∨ (False ∧ False)) → ((p4 ∨ ((p5 ∧ ((p2 ∨ False) ∧ p2)) ∨ (p1 → p3))) ∨ (p4 ∨ p5))) ∨ (True ∨ ((p3 ∧ (False ∧ p3)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190762465264011931537491133822 : (((p5 → ((p2 ∨ p4) → (False → p2))) ∧ (p3 ∨ p2)) ∨ ((False ∧ p1) ∨ ((True → (p1 ∧ (True → (p2 ∨ (True ∨ p5))))) → (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135215488789601923303460803554 : (((((p1 → ((((p3 ∧ p2) ∧ False) → p4) → p5)) → (False ∧ p3)) ∧ (p5 ∧ (p1 ∧ (False → p5)))) → (p4 ∨ p4)) ∨ ((p1 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257499807848045851350955316624 : ((p3 ∨ False) → (((((True → (p1 ∧ p4)) → False) ∨ (p2 ∧ ((p5 ∨ ((False ∧ p3) ∧ (p5 ∧ (p4 ∧ False)))) → True))) ∧ False) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300957771640538170948286490437 : (False ∨ ((((p5 ∧ p4) ∨ ((p2 → p1) ∧ (p5 ∨ (True → p2)))) ∨ True) ∨ (((p1 ∧ p1) ∨ p5) ∨ ((p2 ∨ p2) → (p4 ∧ (p5 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



