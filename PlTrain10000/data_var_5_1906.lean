variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135915319192950477840416167562 : ((((p5 → (p2 ∧ p3)) → ((((p2 ∧ p5) ∧ p4) ∨ False) ∧ p1)) → (((p4 → False) ∧ p5) ∧ (p1 → (p4 ∧ p5)))) ∨ ((False ∧ p4) → p3)) := by
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
theorem thm_5_vars_164459936728090933405972588421 : ((((p3 ∨ (p5 ∨ (((p3 → (p4 ∨ (p1 → (p4 ∨ p1)))) ∨ p3) → p2))) ∧ False) ∧ p5) ∨ ((p2 ∧ (True ∨ p4)) → (p5 → (p5 ∨ True)))) := by
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
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_944645594038339353006822774 : (((False ∨ ((p4 → False) ∧ (((p1 ∨ ((p2 ∨ (True ∧ p5)) ∧ True)) ∨ p5) → ((p4 → (p1 ∨ p5)) ∧ (p2 → p4))))) ∧ p2) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∨ ((p2 ∨ (True ∧ p5)) ∧ True)) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729615774847054414993256007957 : (((((p5 ∨ p3) ∨ p3) → ((((p1 ∨ p4) ∨ (True ∨ (False ∨ ((True ∧ (False ∧ (p2 ∨ p1))) ∨ ((True → p3) → p1))))) ∧ False) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613297054138051620843208540859 : (((((((True → p3) ∨ (p1 ∨ p3)) → (False ∨ ((p1 ∧ p2) ∨ ((((p1 ∨ p5) → p3) ∨ (p1 ∧ True)) ∨ p4)))) → (p3 ∨ p2)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750816657905472653618488220716 : (((True ∧ ((((((p2 → False) ∧ p1) ∧ p2) → (p1 ∧ p5)) → p4) ∧ ((p4 ∨ (p2 ∧ ((False ∧ p3) ∨ p4))) ∨ (False ∧ (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731248454100792106270926741215 : ((((p3 ∨ (False → True)) → ((((p3 ∨ p3) ∧ (((p1 ∧ ((p5 ∧ p2) ∧ (p4 ∧ p4))) ∧ p5) ∧ (True ∧ (p2 ∨ p2)))) ∧ p4) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114873629321774924863070080965 : (((((p5 ∨ p4) ∧ p3) ∧ (True ∧ (False ∧ (((p3 ∧ p3) ∧ False) ∧ True)))) ∨ (p5 ∧ (False ∨ (p3 ∨ ((False → False) ∧ p1))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214791818808366492075708510907 : (((p1 ∨ p2) ∨ (False ∧ p4)) ∨ ((True ∧ ((p2 ∨ (True ∨ (p2 ∧ p3))) ∨ (((True ∨ p4) ∨ p2) → (p4 ∧ True)))) ∨ ((p2 ∧ p4) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49475037481790325878923764678 : ((((((p3 ∨ ((p4 ∨ (p2 → (p4 ∨ p1))) ∨ ((p4 ∧ (p4 ∨ (p4 → p1))) ∨ p1))) ∨ p4) → p2) → p2) → (True → (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108233285682474603066560818042 : ((True ∧ (((p5 ∧ ((False → False) ∧ p5)) ∧ ((False ∧ (p3 ∨ ((True ∨ (((False ∨ p5) ∨ p4) → p3)) ∧ p1))) ∨ p3)) ∨ True)) ∧ (p4 → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355217129280097844449412985231 : (p5 → (((False → (((True ∧ False) ∧ p5) ∧ p3)) ∧ ((((((p1 → p4) ∨ ((p3 ∨ True) → p4)) → p3) ∧ (p4 ∨ p5)) ∧ p4) ∧ p4)) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : ((p1 → p4) ∨ ((p3 ∨ True) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h16 : ((p1 → p4) ∨ ((p3 ∨ True) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h16
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113431824057300557827646038255 : (((((((p1 ∧ ((True → (((p4 ∧ p5) → p2) ∨ False)) ∧ p2)) ∨ p1) → ((p3 ∧ p3) ∧ p1)) ∨ p2) ∨ p2) ∨ (p3 → p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643662168733892628584165542347 : ((((p5 ∧ ((p1 ∧ ((p3 ∧ True) → (((p5 ∧ False) ∨ ((((((p2 → False) ∨ p4) ∧ False) ∨ p1) → p5) ∨ p3)) ∧ p4))) ∧ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803405347047607217170584198025 : (((p3 → ((p4 ∨ ((((True → (((p4 ∧ False) → (((p1 → p1) ∧ False) → p4)) ∧ p1)) ∧ (p5 ∧ (p5 → True))) ∧ p4) ∨ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651230768207921791900921315216 : ((((((p4 ∨ False) ∧ False) ∧ (p3 ∨ (((p5 → ((p5 ∨ (True → (((True → p2) ∨ p5) → p4))) ∧ p4)) ∧ p3) ∨ p1))) ∧ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114189757620198913090004880271 : (((((((p1 → p5) → (p5 → (False → True))) → (False ∨ p3)) → p2) → ((p4 ∨ False) ∨ (p1 → p3))) → (p4 → (p3 ∧ p2))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54505035583804751467160201109 : ((((p1 ∧ (p4 ∧ p3)) ∨ ((p5 ∨ p1) ∧ p2)) ∨ (True ∨ (((p4 → (((p5 ∨ p1) ∨ p3) ∧ ((False → p5) ∧ True))) ∨ True) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172628203209377053255585061367 : (((p3 ∧ False) ∧ (p2 ∧ ((((p3 ∨ p3) → p4) → p1) ∨ (p5 ∨ (p4 → p1))))) ∨ ((True → ((p4 ∧ p4) ∨ p2)) ∨ (p4 → (True ∨ p3)))) := by
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
theorem thm_5_vars_204573553673236472740190142785 : ((((p5 ∨ p3) ∧ (p4 ∧ p3)) ∨ False) ∨ ((False → (p2 ∧ p1)) ∨ (p4 ∨ (p1 ∨ ((p3 ∧ p1) ∨ (p5 ∨ (p3 → (p3 → (False ∧ p5))))))))) := by
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
theorem thm_5_vars_64012334230892100578945065268 : ((False ∨ (((((((((True ∨ p2) ∧ ((p1 ∨ p1) ∨ p2)) ∨ p4) ∨ (p2 ∨ p4)) ∨ False) ∨ p5) ∧ (p1 → False)) → p1) ∨ (p5 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241657629591628337032726768902 : ((False → p5) ∧ (((((True ∨ (p5 ∧ ((p2 ∧ p2) ∧ ((True ∨ False) → p2)))) ∨ p4) → p3) → False) ∨ ((p5 ∧ (p1 ∧ p4)) → (p4 ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692104149999450926542668817793 : (((((p5 ∧ ((((False ∨ p1) ∧ (p4 ∨ False)) → (p2 ∨ True)) → True)) ∧ p3) ∧ (p2 ∧ (p1 ∨ ((p3 ∧ (p2 ∧ p4)) ∧ (p1 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111550247313850693109199231988 : (((((p4 ∨ (p2 → (((p1 ∨ p5) ∨ p5) → (p5 ∨ ((p2 → p2) → ((p5 ∨ p3) → p1)))))) → (p2 → p3)) ∧ False) ∨ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341622163578456213367754137949 : (p2 → (((p2 ∨ True) → (p3 ∨ (((p1 → (p4 ∨ (p5 ∧ ((True → ((False ∧ p1) → True)) ∨ p4)))) → p5) ∨ (p5 ∨ True)))) ∧ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556655057441530371668900629934 : (((p3 ∨ (((True → (False ∨ p3)) ∧ ((((p2 ∧ p1) ∧ True) → (p5 → (((p1 → True) ∧ p3) ∧ p4))) ∨ p1)) ∨ (p3 → (True ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806725252113422484511463772586 : (((p4 → ((((True ∨ ((p2 ∨ p2) ∧ ((p5 → True) ∨ (True → p2)))) ∨ p5) → ((p5 ∧ (p3 ∧ True)) ∧ (p2 ∧ p4))) ∧ (p2 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67597112897766910225903701503 : ((p1 → (False ∧ (((False ∨ (p2 ∧ (((p4 ∧ p4) → p5) ∨ True))) ∨ p1) ∧ ((((True ∨ (p3 → p2)) ∨ (False → True)) → p2) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775300754828590927512914686670 : (((False ∨ (True ∧ ((p5 → (p5 → ((p3 ∧ p3) ∧ p3))) → (((False → p1) ∨ (((p1 ∧ p1) ∨ p1) ∧ (p3 → True))) → (False ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119389737923334006620232349282 : ((p4 → ((((p5 ∧ p3) → (p1 ∨ (p5 ∧ ((p4 ∨ False) ∧ (p2 → (True → (((p2 ∨ False) → p3) → True))))))) → p1) ∧ p5)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716511045153725607067528895733 : (((((p1 ∨ False) ∨ (p2 ∧ p1)) ∧ (((True → False) ∨ (False ∨ (True → True))) ∨ ((((False ∨ (p1 ∨ p4)) ∨ p1) → (False ∨ p2)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636447861344569347133541208595 : (((((p4 → ((p5 ∨ ((p2 ∨ True) → (p3 ∧ (False ∨ p4)))) ∧ ((p4 ∧ p3) → p2))) → ((True ∧ (True → p2)) ∨ (p5 ∧ p2))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149659734979027761618395720910 : ((p4 ∧ (p1 ∧ ((False ∨ ((((p4 ∨ ((True → ((True ∧ True) ∨ True)) ∧ False)) → False) ∧ False) ∨ False)) ∧ p2))) ∨ (p3 → ((p1 ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260474127951456193500411709709 : ((p3 → False) → ((((((p2 ∨ ((p1 ∧ p5) ∧ p4)) ∧ p2) → p5) → (p5 ∨ (p3 ∧ ((p3 ∨ (p5 ∧ p5)) ∧ p5)))) ∨ True) ∧ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140480167403840342921889133867 : ((((p4 → (p5 ∧ (((p5 ∨ (p1 → True)) ∨ p2) → ((p4 ∨ p2) → p1)))) ∧ p5) ∧ (p3 → ((p4 ∧ True) ∨ p1))) → (p5 ∨ (p3 → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244282250635030262378251592764 : ((False ∧ True) ∨ ((p4 ∨ True) ∧ (((True → ((((p5 → p2) ∧ p4) ∨ p3) ∧ (p4 → p5))) ∨ True) ∧ (p4 ∨ ((p5 ∨ (p5 ∨ p1)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248199243920629097516139947906 : ((p2 ∨ p1) ∨ (((p3 ∨ p3) → ((((True ∨ (p1 ∧ ((p2 → True) ∧ (p4 ∨ False)))) ∧ ((p3 ∧ (p5 → False)) ∧ p1)) ∧ p3) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680080429859174727201208415214 : (((((p3 → ((((p3 ∧ p4) → p5) ∨ True) ∧ (((p3 ∨ (p4 ∨ p1)) ∧ (False ∨ False)) ∨ p1))) → False) → (((p3 → p4) ∨ p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341086361709444451387426915643 : (p2 → ((p1 → ((((p3 → (p5 ∧ p1)) ∨ p2) → (p5 ∧ (True → (((p5 ∨ False) → ((p1 ∧ False) → p5)) ∧ (p1 → p3))))) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142379205244525840848431902214 : ((p4 ∧ (((((False ∨ p4) ∧ (p2 ∧ True)) → (((p1 ∧ ((p4 ∧ p5) → True)) ∧ p4) ∨ p2)) ∧ (p3 ∨ True)) ∨ p3)) → ((True → p3) → p3)) := by
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
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634541985501228551933445298550 : (((((((p2 → p1) → True) → (((p4 → (False → (p1 ∨ True))) → p5) ∧ ((False → (p4 → p3)) ∨ p2))) ∧ (p2 ∨ (p5 → p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55017234809706914127202317477 : (((True ∧ (p2 ∨ (False ∨ (p5 → True)))) ∧ ((p1 ∧ (((p1 ∨ p5) ∨ False) ∨ ((p1 → p1) ∧ ((p2 ∨ (p3 → p1)) ∧ p5)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353552221544679900766016282960 : (p4 → (p3 ∨ (((p5 ∨ ((p2 → p5) ∨ (p2 ∨ p2))) ∨ (p4 ∨ (False ∨ ((True ∧ p5) → False)))) ∨ (p4 → ((p4 → p5) ∧ (p4 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116812591638822475319294694971 : (((p3 ∨ p5) ∨ (p2 → (((((p5 → (True ∨ False)) ∨ p2) → ((p5 ∧ False) ∧ p4)) ∨ ((True ∨ False) ∧ (p3 → p1))) ∧ p4))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44370730185078088270406098192 : (((((p2 ∨ p3) → (p5 ∨ (p3 → (p4 → (p4 ∨ ((p3 ∧ False) ∨ p4)))))) ∧ (True ∨ (True ∨ ((True ∨ False) ∨ (p3 → p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317626731739927705837670339677 : (p4 ∨ ((((p1 → ((p1 ∨ ((p4 → ((p4 → ((p5 ∨ (p1 ∧ p1)) ∧ p3)) ∨ (p5 ∧ p1))) ∨ p5)) ∧ p4)) → (p3 ∨ p3)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145306217616536106579498571337 : (((((p4 ∨ p1) ∧ p2) → (p3 ∨ p3)) ∨ (p1 → (p3 → (True ∨ ((True ∨ p5) → ((p4 ∨ False) → p4)))))) ∧ (p4 ∨ (False → (p1 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51118931452636085404957819771 : ((((((((p2 ∨ True) → (p2 → p1)) ∨ p3) → ((True → p3) → p3)) → (p5 → False)) ∨ False) ∨ ((p3 → (p5 ∨ False)) → (True ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219773083752946941543392392219 : ((p2 → ((False ∨ p2) → p4)) → (p4 → ((((p4 → (p1 ∧ (((p5 ∨ (True → (p1 ∧ True))) ∧ p1) ∧ False))) ∨ True) ∨ True) ∧ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215931997120633812230410920441 : ((p3 ∨ (p5 ∨ (p4 ∧ False))) ∨ ((p5 ∧ (p2 ∨ False)) → (p5 → ((p4 ∨ (p5 ∨ (((((p2 → p5) ∨ p4) → True) ∧ p1) → p4))) ∧ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151851491803072671492071364745 : ((((p1 ∨ (((p1 → (p4 → p2)) → (p1 ∨ p4)) ∨ p5)) → (p3 ∧ p2)) ∨ (p4 ∨ (p1 ∨ (p2 ∧ p1)))) → ((p2 ∧ (False → p2)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347284599536201061542995576343 : (p3 → (((p5 → ((p1 ∨ (p3 ∧ p2)) ∧ p3)) → (p4 ∧ p2)) ∨ ((False → False) ∨ (False ∨ (p1 → ((((p1 → p1) ∨ p4) → p1) ∧ p2)))))) := by
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
theorem thm_5_vars_49516121522255908733431366953 : ((((((p3 ∧ (p5 ∨ (p5 → False))) ∧ p1) → (p2 → (False ∧ ((p1 ∧ (p2 → p1)) ∨ False)))) ∧ (p5 → p1)) → ((p3 → p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603096811213428603730327441129 : ((((p2 ∨ (((((((False ∨ (True → p3)) ∧ p2) ∧ p1) → p5) → p2) ∨ ((((p1 ∧ p5) ∨ True) → (p5 ∧ p4)) ∨ True)) ∧ p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354672422467287392878261027651 : (p5 → (((True → (((p4 ∨ False) → p4) → (p3 ∧ ((((p3 → ((p2 → True) ∧ True)) ∨ p1) → (True ∨ (False → p1))) ∧ p4)))) → p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172532693429825860457195987522 : (((False → (True ∨ p1)) ∧ (p2 → ((p1 ∨ p4) ∨ (p3 → ((p5 ∨ p5) ∨ p4))))) ∨ (False → ((p4 → ((p3 ∧ (True ∨ p5)) ∨ p5)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53710226575595016178734891741 : (((p2 ∨ (((p2 → p1) ∧ p4) ∧ ((p1 ∧ p5) → True))) ∧ ((((p3 ∨ p1) ∧ True) ∨ (p1 → ((p4 ∧ p1) ∧ False))) → (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_534096165633300284827017168 : ((((((((p5 ∧ (True ∨ (p2 ∧ p1))) ∨ ((((False → False) ∨ p3) → p5) → p3)) ∧ (p3 → False)) ∨ p4) → p5) → p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55060572871353781364475210568 : (((p2 ∨ ((p2 ∧ p1) → (p2 ∧ True))) ∧ (((((False → p5) → ((p3 → (p1 ∨ False)) ∧ (p5 → p4))) ∨ True) ∨ (False ∨ p5)) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43343210250906542003812674477 : (((((False ∧ ((((True → p1) ∧ p4) ∧ (((p2 ∨ p5) ∨ (p3 ∧ True)) → ((p4 ∨ (p5 → p1)) ∧ p3))) ∧ p4)) → p5) ∨ False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634926303518320970516931880344 : (((((p4 ∨ ((((False ∨ (False → (p1 ∧ True))) → p5) ∧ ((True ∧ p4) ∨ (p2 → p5))) ∨ (p5 → p1))) ∨ ((p2 ∧ p5) → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678862003388747203084711301867 : ((((p1 ∧ ((p4 ∨ p4) ∧ ((p4 → (((((p5 ∨ p2) → (p2 ∨ False)) → True) → p1) → True)) → p2))) ∨ (p3 → (p4 ∧ (False → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240026821784235456964807275875 : ((p4 ∨ True) ∧ ((p1 ∨ ((p1 ∧ p1) → False)) ∨ ((p1 → (((False → (p4 ∧ (p4 ∨ p4))) ∧ (p5 → ((p2 ∨ False) ∨ p2))) ∨ p1)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352249555015792555197040358511 : (p4 → ((p3 ∨ (p4 ∧ (p5 ∨ p5))) ∨ (p4 → ((((p2 → (((False ∧ p3) ∨ p2) → p4)) → p1) ∨ (p4 ∨ (p2 ∨ (True ∨ p1)))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59066740025779586975905354795 : (((p5 ∧ True) ∨ ((p2 ∧ p2) ∨ (p5 → (((p3 → ((True → ((((p4 ∧ p3) ∧ False) ∧ (False → True)) ∧ p3)) → p2)) ∨ p3) ∨ p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640920303658452892628625141357 : (((((True ∧ p1) ∨ (p1 → (((p2 → False) → ((p3 ∧ False) ∧ p4)) → ((False → (False ∨ p4)) → (False → (p4 → (p2 ∧ True))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49557135870355450909581990974 : ((((((p3 → (p2 → p1)) ∧ (p3 → ((True → p1) → True))) ∨ (p5 ∨ (True → p2))) ∨ (False → (True → False))) → (p3 ∧ (False → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862894014354825618631742116 : ((p4 ∨ ((((p3 ∨ ((p4 ∧ (p1 ∧ ((p5 ∧ False) ∧ (p5 → p5)))) ∧ p3)) ∨ (True ∨ (True ∨ p5))) ∨ p2) ∨ (p2 ∨ False))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314682842949698116745928808994 : (p3 ∨ ((((True ∨ (((p3 ∧ (True ∨ p2)) ∨ p5) ∨ p1)) ∨ p5) ∧ (p4 ∨ (False ∧ p5))) → (False ∨ ((p3 ∧ False) → ((p1 ∧ p1) ∨ p2))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h20
              -- Conjunctions on the left can always be decomposed.
              let h21 := h20.left
              let h22 := h20.right
              -- False on the left can always be used.
              apply False.elim h22
            case inr h23 =>
              -- Conjunctions on the left can always be decomposed.
              let h24 := h23.left
              let h25 := h23.right
              -- False on the left can always be used.
              apply False.elim h24
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- Conjunctions on the left can always be decomposed.
              let h29 := h28.left
              let h30 := h28.right
              -- False on the left can always be used.
              apply False.elim h30
            case inr h31 =>
              -- Conjunctions on the left can always be decomposed.
              let h32 := h31.left
              let h33 := h31.right
              -- False on the left can always be used.
              apply False.elim h32
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h36
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- False on the left can always be used.
            apply False.elim h40
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h44
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- False on the left can always be used.
          apply False.elim h46
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h47.left
          let h49 := h47.right
          -- False on the left can always be used.
          apply False.elim h48
  case inr h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h51 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h52
      -- Conjunctions on the left can always be decomposed.
      let h53 := h52.left
      let h54 := h52.right
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h55.left
      let h57 := h55.right
      -- False on the left can always be used.
      apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57730533219285764077493312145 : ((((p2 ∨ p3) → False) → ((False ∧ ((p4 ∨ ((p2 → (False ∨ False)) ∧ (((p2 ∧ False) ∨ (False ∨ p3)) → p1))) → p5)) ∨ (False → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204351133525062540435446864937 : (((False ∨ (p1 ∧ (True → True))) ∧ p2) ∨ (((p2 ∨ (p1 ∨ ((p5 ∨ (p1 → (p5 ∨ True))) → (p2 ∧ (True → p5))))) ∧ p5) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146994502127750701551655515450 : ((((((((p4 ∧ p5) ∧ ((p4 ∧ ((False ∨ p2) ∧ p1)) ∧ True)) → p4) → p2) ∧ p5) ∧ (p1 → False)) ∧ p4) ∨ ((p1 → True) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666518153258265808916038275702 : ((((((p1 ∨ (p5 ∧ ((p4 → False) ∧ True))) ∨ ((p4 ∨ (p2 ∧ True)) ∧ p5)) ∨ ((p3 ∧ (False ∧ False)) → True)) ∧ (False ∧ (False ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777338477550395112012041186995 : (((p1 ∨ (((((((p1 ∨ p2) ∧ p1) ∧ (True ∧ p3)) → p3) ∧ p3) ∧ (p4 ∧ (False ∧ (p2 ∨ p2)))) ∨ ((p5 ∧ (p5 ∨ True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_894427983378270335171500381254 : ((((p2 ∨ ((p5 ∨ (((p1 → (True ∧ p2)) ∨ ((p4 → p2) ∨ p1)) ∧ ((True ∧ False) → (p5 ∧ p5)))) ∧ p4)) ∧ ((p3 → True) → False)) → p3) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h19
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : (p3 → True) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h26 := h3 h24
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h28 : (p3 → True) := by
            -- Implications on the right can always be decomposed.
            intro h29
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h30 := h3 h28
          -- False on the left can always be used.
          apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179617388862045781983949671803 : ((p4 → (((p2 ∧ (False ∧ (False ∨ (p3 ∨ (p4 → p1))))) ∨ False) ∨ True)) ∨ ((True ∧ p2) → (((p3 → (True ∨ p4)) ∧ False) ∧ (p2 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789471261188389475046079096767 : (((p5 ∨ ((False ∨ ((True ∧ (p3 ∨ p5)) → (p5 ∧ ((p4 ∨ p2) → True)))) ∨ (p2 ∨ ((((p2 ∧ p5) ∨ p3) ∨ p4) ∨ (p5 → p5))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159305040763274208383272920485 : ((p5 → ((((p2 → ((True ∧ (p5 ∧ p2)) ∨ (True ∧ p5))) → (False ∧ (p1 → p4))) ∧ p1) ∨ p1)) ∨ (False → (False → (p3 ∨ (p4 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142548369138722761331052445580 : ((True ∨ ((p5 ∨ p1) ∨ ((((p4 → p3) ∧ p1) → False) → (((((p5 → (p4 ∧ False)) ∧ p2) ∧ p2) → p2) → p1)))) → ((p3 → p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322399609240756377889719538590 : (p5 ∨ (((True → (((p4 ∧ p5) ∧ False) ∧ ((p4 ∧ p3) ∨ (p1 ∨ (True ∧ p4))))) → ((False ∧ (True ∧ (p3 ∨ (p4 ∨ p1)))) ∨ p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342969464426547024578844651901 : (p2 → (((False ∨ (p4 ∨ p3)) ∧ p1) ∨ (p4 → ((p5 ∨ (p2 ∧ (True ∧ True))) ∨ ((p2 → (p2 → (True ∧ (True → p5)))) → (p5 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60364219267136649043690001645 : (((p3 → True) → (((p1 ∨ False) → (True → (((False ∧ ((p1 ∨ p1) ∨ (p5 ∨ False))) ∧ p1) ∨ False))) ∧ (p4 ∨ (True ∧ (p5 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261639224281336687762761307014 : ((p5 → p5) → (((((p3 → ((p2 → p4) ∧ True)) → p3) ∨ (False ∨ p2)) ∨ (p3 ∨ True)) ∨ ((((p1 → p1) ∨ (p3 ∨ p3)) ∨ p2) ∧ p1))) := by
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
theorem thm_5_vars_171520591381135114938825763324 : ((((p4 ∨ (((p5 ∧ ((p3 ∨ p4) → False)) ∧ (True ∨ p4)) ∨ False)) ∧ False) ∨ p4) ∨ ((p4 ∧ ((p5 ∧ p1) ∧ ((p2 → p1) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199839215405881032254867503833 : ((((p1 → False) → (False → p3)) ∧ (p5 → p4)) → ((False ∨ (((p3 → p4) → False) ∨ ((p1 ∧ (p1 ∨ (p1 → p5))) → (False → p1)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310253648103296637107084758566 : (p2 ∨ ((p4 ∨ ((((p1 ∨ ((p2 ∧ True) → True)) ∧ p4) ∧ p5) ∧ p3)) → ((((False ∧ p1) ∧ True) ∧ (((p4 ∨ p5) ∨ True) ∨ p1)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
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
theorem thm_5_vars_55122098354468581278849926962 : (((((p3 ∧ p3) ∨ (p3 → p1)) ∧ p2) ∨ (((False ∧ (p3 → False)) ∨ (((True → (p1 ∧ p4)) → (False → p3)) ∨ (False ∨ p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40443282976887193117457369025 : (((((((p3 ∧ False) ∧ (p5 ∨ (p1 → p4))) → True) → (p3 ∧ ((((False ∧ True) → p2) ∨ ((False ∧ False) ∨ p4)) → True))) ∨ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39071767320528641639798519207 : ((((False ∨ p2) ∨ ((((p2 → p3) ∧ (((p5 ∧ p3) ∧ (p3 ∨ False)) ∧ p4)) ∨ (((p2 → (False ∨ p5)) → p5) → p2)) ∧ p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76957191590672080077089079433 : ((((((False ∨ ((p3 ∨ True) → p1)) ∨ p1) ∨ p3) → (((p2 ∨ (True ∨ (p1 → p3))) ∧ ((p2 ∨ p1) ∨ (p2 ∨ True))) ∧ True)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ ((p3 ∨ True) → p1)) ∨ p1) ∨ p3) → (((p2 ∨ (True ∨ (p1 → p3))) ∧ ((p2 ∨ p1) ∨ (p2 ∨ True))) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h7 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111509855413768808071513024308 : (((p4 → (p2 ∨ (((True ∧ p3) → ((((p4 → (p3 → p4)) ∨ False) ∧ p4) ∨ True)) ∧ ((p2 ∧ (True → p4)) → False)))) ∧ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_945120411162784437279635848044 : (((((False ∧ p1) ∧ (p4 ∨ p3)) ∨ ((p5 → (p1 ∨ (((p4 ∨ p2) ∨ (((False → p5) ∧ (p1 ∨ p5)) ∨ p5)) ∧ (p3 → p3)))) → False)) → p2) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p5 → (p1 ∨ (((p4 ∨ p2) ∨ (((False → p5) ∧ (p1 ∨ p5)) ∨ p5)) ∧ (p3 → p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h8
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330922814836313728496344988634 : (True → (p4 → (((p3 ∧ ((p4 ∧ p3) ∧ (p3 → p5))) ∧ ((((False ∧ p1) → p4) → False) ∨ p1)) ∨ ((p2 ∧ p1) → ((p2 ∧ p2) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105507017504889253369413900851 : (((p1 ∨ ((p2 → (p2 → ((p3 ∨ False) → (((True → True) → p3) → False)))) ∧ (p4 ∨ p1))) ∨ ((p3 ∧ (True → p4)) → True)) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300136073105993971722276113671 : (False ∨ ((False ∧ (((p4 ∨ (p5 ∧ (True ∨ (p5 ∧ ((p1 → (p5 → (p1 ∧ False))) ∨ False))))) → (p3 ∨ (p3 → p1))) ∧ p1)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259517981219310658121751660851 : ((False → p5) → ((((p1 ∨ ((p4 → p4) → p1)) ∨ p1) ∨ p4) → (((p1 ∨ ((p3 → ((p5 → (False ∧ p1)) ∨ p3)) ∨ p3)) ∧ p4) ∨ True))) := by
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117177532865441067463575804970 : ((True ∧ (((((False ∨ (p5 ∧ (p3 ∨ (((p4 ∧ False) ∧ p3) ∧ True)))) → p2) ∨ p5) ∧ ((p3 ∨ p5) ∧ p3)) ∧ (p3 → p4))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205510359661138860443633549036 : (((p4 ∧ p3) ∧ (p1 ∧ (True → False))) ∨ (p3 ∨ (p2 → (((False ∨ (False → p1)) ∨ (p2 → p1)) ∨ ((p5 ∧ (True → p4)) → (p2 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350988791207039281438914379181 : (p4 → ((True ∧ (((p3 → (p3 ∨ (True ∨ p4))) → p2) ∧ (((True → False) → (p2 ∨ False)) → (p4 ∧ (p1 → (p5 ∧ False)))))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689022300911795563451881348528 : (((((((((p2 ∧ p3) → True) ∨ False) ∧ (p2 → (p5 ∧ p3))) → (p5 ∨ False)) ∨ p2) ∨ ((p2 ∧ ((p1 → (p5 ∧ True)) ∨ False)) ∨ True)) ∨ p1) ∧ True) := by
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



