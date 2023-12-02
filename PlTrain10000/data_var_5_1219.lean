variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257196539940979332275728844828 : ((p2 ∨ p2) → ((((p5 ∨ (p5 ∨ ((p3 ∧ True) ∧ (p3 ∧ (p3 ∧ p1))))) ∨ ((p5 ∧ (p2 ∧ False)) ∨ False)) ∧ (p4 ∨ True)) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694992905764652352842396283914 : (((((((((p4 ∨ p3) ∧ True) ∨ p3) → False) ∨ (p1 ∧ (False → p1))) ∧ p3) → (((((False ∨ True) ∨ p3) → p2) ∨ True) ∧ (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215946844470418505553670839905 : ((p4 ∨ ((p4 ∧ True) ∧ False)) ∨ (p1 ∨ ((p4 ∧ p1) ∨ ((((True → p3) ∧ (True ∨ (p3 ∨ (False ∨ p4)))) ∧ (p5 ∧ p2)) → (False → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225215112573435576891642207613 : (((p5 ∧ False) ∧ p2) ∨ ((((False → True) ∧ (p4 ∧ ((p1 → (((p2 ∨ p5) ∧ p3) ∨ False)) ∧ (p2 → p5)))) ∧ (False ∧ p4)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704381770148049421061109639450 : ((((((False ∧ False) ∨ p5) ∧ (True → (p3 → (p3 → p4)))) → (p2 ∨ (((True ∨ ((p5 ∨ p4) ∧ ((p1 ∧ p1) → p4))) → p4) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52590134481136548883692266860 : ((((((p1 ∧ (p4 → (p5 ∨ p5))) → p2) ∧ p2) → (p5 ∨ (True → p1))) ∨ (((p3 → p2) ∧ p3) → ((p1 ∧ (p4 → p1)) ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748882797129102125413778968841 : ((((p4 → p1) → (p5 ∧ (((p2 ∧ ((True → (False ∧ (p1 ∨ p2))) ∨ False)) ∧ (p5 ∧ p5)) → (p1 ∧ (False ∧ (False ∨ (p2 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313951300954538113934096926509 : (p3 ∨ (((p3 → (p1 ∨ (((((((p5 ∧ (False ∨ p5)) ∨ True) ∨ p1) → p1) ∨ False) ∨ (True → p5)) ∨ (p5 ∨ False)))) → False) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258778670988723910460953255403 : ((True → False) → (((p3 ∧ ((p1 ∧ p5) → (p3 → p3))) ∨ (p5 ∧ ((((p1 ∨ p1) ∧ False) ∨ False) ∧ (p3 → p4)))) ∧ ((True ∧ False) ∧ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117741315565745971116946082712 : ((p4 ∧ (((p3 → p1) ∨ (p4 ∧ ((False ∨ (((p3 ∨ False) → (((p3 → (p5 ∨ p3)) ∨ p3) ∧ p5)) ∨ p2)) ∧ p1))) ∧ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328406904477268094298664328774 : (True → (((p3 → (p5 → (True → ((False ∧ p1) ∨ (((p1 ∧ p2) ∧ (p4 → p1)) ∨ p5))))) ∨ p3) ∨ (p3 → (False → (p5 ∨ (True → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346794552690231303793829912209 : (p3 → ((True ∧ (((p5 ∨ ((p2 ∨ p1) → (p4 ∨ (p5 → ((p2 → (p4 → p2)) → p5))))) → p4) ∧ p3)) ∨ ((False ∧ False) → (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200278571188719979018777005525 : (((False → (False ∧ False)) → (p3 ∨ (p5 ∧ p3))) → (((p5 ∨ p1) → False) ∨ (((((((p2 ∨ p3) ∧ p1) ∧ p4) → p1) ∨ p5) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350226623418508183668752585889 : (p4 → (((p5 ∨ p1) ∨ (((True ∨ (p1 ∧ (p1 ∨ (p1 ∧ p3)))) ∧ (False → False)) → (p1 → (p5 ∧ ((p2 ∨ True) ∧ (p4 → p3)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264425385114926393372864678951 : (True ∧ (((False → (True ∨ p3)) ∧ p2) → (((p1 ∧ (((p1 → p3) ∨ p5) → p1)) ∨ (((p5 ∨ p1) ∨ p3) → ((p1 ∨ p2) ∨ False))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199934938661489036313024923139 : (((True ∧ ((p4 → p4) → p1)) ∨ (p2 → p1)) → ((False ∨ ((((p1 ∧ True) → (p3 → p3)) ∨ True) → ((p4 ∧ (p3 → False)) ∧ False))) → p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (((p1 ∧ True) → (p3 → p3)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (((p1 ∧ True) → (p3 → p3)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58946829723232078975394582759 : (((p2 ∧ True) ∨ (((((p5 ∧ True) ∧ p4) ∨ p3) ∧ (((p5 → True) ∨ ((p2 ∧ (True → (p3 ∧ p3))) ∨ p1)) ∧ p4)) → (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171618695098247754705290081409 : (((((p4 ∨ p1) ∨ True) ∧ (p3 ∨ ((p1 ∨ (p4 ∧ (p4 → p1))) ∧ False))) ∨ False) ∨ ((p3 ∧ p5) ∨ ((p1 ∧ p4) → (p1 ∨ (p1 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139260376307649951117422926022 : ((((True → True) → (((True ∧ (p3 ∧ ((((p5 → p3) ∨ (False ∧ (p1 → p2))) → p5) → p4))) ∨ p3) ∧ True)) ∨ p1) → ((p3 → False) ∨ True)) := by
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
theorem thm_5_vars_124220257533317643342755905803 : ((((((p4 ∨ (p3 ∧ (False ∨ True))) ∧ p5) ∨ p3) ∨ p1) → ((False ∧ False) ∧ (p3 ∨ (((p2 ∧ (True → False)) ∨ p5) ∨ p4)))) → (p1 → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p4 ∨ (p3 ∧ (False ∨ True))) ∧ p5) ∨ p3) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791035514059623791652679354628 : (((True → (((((((((p2 ∨ (True ∧ p4)) ∧ p3) → p4) ∨ False) → (((p5 ∧ (False → False)) → p3) ∨ p3)) ∧ p3) ∧ p3) → False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136953005972979183677754670631 : (((True ∧ p2) → ((((p2 → (((False ∨ (p3 → (False ∨ p1))) ∧ p5) ∨ (p4 ∨ True))) ∨ False) → p4) ∨ (p2 ∧ True))) ∨ ((p2 ∧ p5) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701644153511742410470322139185 : (((((p3 → p3) ∨ ((((True → False) ∨ p5) ∧ p3) ∧ p5)) ∧ (((p3 ∨ p5) ∧ p1) → (True → ((p2 ∨ (p2 → p1)) → (p5 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71384370348247190065669100427 : ((((p1 → False) ∧ (((((p5 ∧ ((p1 ∧ p2) ∧ True)) ∨ (((True ∧ (False ∧ (p2 ∧ True))) → p3) ∧ p3)) ∨ p5) ∨ p4) → p2)) ∧ p3) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((p5 ∧ ((p1 ∧ p2) ∧ True)) ∨ (((True ∧ (False ∧ (p2 ∧ True))) → p3) ∧ p3)) ∨ p5) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746839936237742093877289440799 : ((((p3 ∨ p5) → (True → ((((p4 ∨ ((((True → p2) ∨ (p1 → (False ∨ (p5 → p2)))) → False) → (False ∧ p5))) ∨ p3) ∧ True) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350984340554111197392215272941 : (p4 → (((p2 → p3) ∨ ((p1 ∨ ((False ∧ (p2 → (p3 ∨ (True ∧ ((False ∨ p2) → True))))) ∨ (p2 ∧ False))) ∨ (p1 ∨ False))) ∨ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157208121727545845546873282923 : ((((((p4 ∨ (p1 ∨ (p4 → True))) ∨ (p1 ∧ (True ∧ p1))) → (p3 → False)) → (p1 ∧ p5)) → False) ∨ ((((False → p1) ∧ p3) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314526187922171384049165450980 : (p3 ∨ ((p4 ∨ (((p1 ∨ ((p5 ∨ p2) ∨ p4)) ∧ (((True → p2) ∨ p1) ∧ p5)) ∨ (False → False))) ∧ ((((p5 ∧ p3) → p4) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781503138715073356667675640071 : (((p2 ∨ (p5 ∧ (p1 → ((((p5 → (False ∧ ((p3 → p5) ∧ p1))) ∧ False) → (((p2 ∧ (True ∨ p5)) ∧ True) ∧ (True ∧ p4))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206647769344393066399420660886 : ((p1 → (p4 ∧ ((True ∧ True) ∨ p4))) ∨ (((p4 → p3) ∨ ((((True → p3) ∧ (False → p4)) → p1) ∨ ((p3 ∧ p4) ∧ p2))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63883259360093641440706200551 : ((False ∨ ((((True → p4) ∧ ((((p5 → (p1 ∨ (p2 ∧ True))) → (p5 ∧ ((p5 ∨ (True ∨ False)) ∨ p4))) ∧ p2) ∨ p2)) ∧ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116867409707093344231266243035 : (((p1 → p5) ∨ (p2 ∧ ((p5 ∧ ((p2 ∨ True) → ((p4 ∨ ((p4 ∨ True) ∨ p3)) ∨ p5))) ∧ (((p5 ∧ p2) → p4) → False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65151127291701767433869490200 : ((p2 ∨ (p5 → ((((((p1 ∧ (((p5 ∨ ((p1 → (p3 → p5)) ∨ False)) → False) ∨ p5)) ∨ p1) → (False ∧ True)) ∧ p3) ∨ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720385577333486881281958254944 : ((((((p1 ∨ p4) → p5) ∨ p4) → ((False ∧ (p3 ∨ (((p3 ∨ ((p2 → (p5 → (False → False))) → p5)) ∧ False) ∧ p3))) ∧ (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157852324690388708540826085175 : ((((p3 ∧ (p4 → p1)) ∧ ((True ∨ (True → p3)) → False)) ∧ (p2 ∨ ((p5 ∧ (False ∨ p4)) ∧ True))) ∨ ((p1 ∧ (p5 → p2)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54423135003418957273397353975 : (((((((p3 ∨ p1) ∧ True) → p3) → p1) ∨ p5) ∨ ((((p2 ∧ p3) → p2) → (True ∧ ((((p5 → p4) → p5) ∨ p2) → True))) ∨ p1)) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319773913832007568709262390649 : (p4 ∨ (((p4 ∨ ((p5 ∨ False) → True)) ∨ False) → (p5 ∨ (p1 ∨ (p3 ∨ ((p1 ∨ p1) → (p4 → ((p2 ∨ ((p2 → p1) ∨ False)) ∨ p3)))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193963631224244658468107899498 : ((p2 ∨ (p2 → (((True ∨ (p4 ∧ p3)) → p3) ∨ p4))) → (((((((p3 → p3) ∨ True) ∨ p1) ∧ p5) → ((p2 → p3) → p4)) ∨ True) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87990851679534942482746956290 : (((p5 → (p2 ∨ (p4 → (p4 ∨ p1)))) → (((p2 ∧ ((((p2 ∨ (p4 ∨ False)) ∧ p1) → True) ∧ ((p5 ∨ p2) ∧ p4))) ∧ False) ∧ p3)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p2 ∨ (p4 → (p4 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705263647737773625012436148889 : (((((p5 ∨ ((True ∨ (True → p4)) ∨ True)) ∧ True) ∧ ((True ∧ ((((p1 ∨ True) ∧ p1) → (p5 ∨ p4)) ∧ (p4 → p5))) ∨ (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64528859103965775016148880243 : ((p1 ∨ ((((p1 → (p2 ∨ True)) ∨ p5) → (p3 → p1)) ∧ ((p3 ∨ (p4 ∨ p2)) ∧ ((True ∧ ((p3 → (p2 → p2)) ∧ p4)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669611184506056205845526042788 : ((((((p3 ∧ (((((True ∧ False) ∨ p2) ∨ (False ∧ (p5 ∧ p3))) → p2) → p3)) ∨ True) ∨ ((p3 → p4) ∨ p5)) ∨ ((False → p3) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246350447202280258904281707573 : ((p4 ∧ p5) ∨ ((False → False) → ((p5 ∧ p5) → ((p2 → (False ∧ (False ∨ ((False ∧ (p4 ∧ True)) ∨ p2)))) ∨ (((p4 ∨ True) ∧ p3) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698470696189468945966583848495 : (((((p1 ∨ (p2 ∨ ((p5 ∨ p3) ∧ False))) ∨ ((p1 ∨ False) ∨ p3)) ∨ (p5 ∧ (((p2 ∨ p1) → False) ∨ ((p2 ∧ p2) ∨ (True → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208428122606044703227964217591 : (((p4 ∨ True) ∨ ((p1 ∨ p5) ∨ True)) → ((((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) → p2) → (((True ∧ False) → p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : ((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : ((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : ((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : ((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : ((((p5 → True) ∧ p5) ∧ ((True → p4) ∧ True)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55282335877306688273046873897 : (((False ∧ ((False → p2) → (p3 → p1))) ∨ ((False ∨ True) ∧ (((p3 ∧ p3) ∨ p4) → ((p5 ∨ p1) → ((p3 ∨ (False → p2)) ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310336237689358777568053134039 : (p2 ∨ (((True ∨ p3) ∨ (p2 → ((p1 → (p1 → False)) ∧ False))) → (((p1 ∧ ((False ∨ ((True → p2) ∧ p3)) → (p2 ∨ True))) ∧ False) ∨ True))) := by
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
theorem thm_5_vars_233411902887433763065622302437 : ((False ∨ (p2 ∨ False)) → ((p5 ∨ ((True ∧ (((True ∧ ((p5 ∨ ((p4 ∨ p5) ∨ False)) ∨ (p5 ∧ True))) ∨ p1) ∧ (p3 ∧ p1))) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87377866034945038585967558700 : (((True ∧ (p1 ∧ ((p1 → True) → False))) ∧ (True ∧ (False → ((p1 ∧ (p3 ∨ (((p1 ∧ (p3 ∧ p5)) ∨ p5) → p1))) → (p2 ∧ p4))))) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135038552578931295071474698392 : ((((False ∧ ((p4 ∨ (((True ∨ (p5 ∨ p3)) → (p5 ∧ (False ∨ p3))) ∧ p5)) ∨ (p3 ∧ p4))) ∧ p2) ∨ (p3 ∨ p2)) ∨ ((False ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612840044370520424330739399939 : (((((False ∧ (((p3 ∨ (p3 ∨ (True ∧ p1))) ∧ p4) → (p5 ∨ ((((p3 ∧ (p4 ∨ p2)) ∧ p3) ∧ p2) → p3)))) ∨ (True → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656194623320093381757038539636 : (((((p5 → ((False ∧ p5) ∨ (p2 → ((p3 ∨ ((p5 ∨ p4) → True)) → False)))) ∨ (((p3 → (True ∧ True)) ∧ p2) → True)) ∨ (p3 ∨ p2)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139444532073758994553341605128 : ((((((True → ((True → (p5 → (False ∧ p2))) ∨ (p1 ∨ ((p2 ∧ p4) → p5)))) ∨ (p2 ∧ p4)) ∨ p1) ∨ True) → p1) → (True ∧ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → ((True → (p5 → (False ∧ p2))) ∨ (p1 ∨ ((p2 ∧ p4) → p5)))) ∨ (p2 ∧ p4)) ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338411719506404491215019413167 : (p1 → (((True ∨ p5) ∨ (p2 ∧ p3)) → ((False ∨ (p5 ∧ (((((p1 ∧ False) ∨ (p3 ∧ ((p4 ∧ p4) ∨ p1))) ∧ True) ∨ p5) ∨ p1))) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299334339548123308503156127570 : (False ∨ ((((p1 ∧ False) → (p5 ∨ p2)) → (p3 ∨ ((False ∧ (p5 ∧ (p1 ∧ ((((p4 ∨ False) ∨ p5) ∨ p3) ∨ p4)))) ∧ (p3 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790721203337646591092301920351 : (((p5 ∨ (True → (((p2 → p3) ∨ (((p2 ∧ ((p5 → p3) ∧ False)) ∧ (p5 ∧ p5)) ∧ (((p5 ∧ p3) ∧ False) ∧ False))) ∨ (False ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49710439101326140057258057608 : ((((p5 → p1) → ((True ∨ ((((p5 → (p4 ∧ p5)) ∨ p4) ∨ (p5 ∨ ((p3 ∧ True) ∨ p4))) → False)) ∨ p2)) → (p5 ∨ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135744416497950602828136006825 : ((((False → ((False ∨ p4) ∨ (p2 ∧ p5))) → (p5 ∧ (False → (p2 → p1)))) ∨ ((p1 ∨ p2) ∧ ((True ∨ False) → p5))) ∨ (p4 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356360902343764439120428782649 : (p5 → (((p5 ∨ p5) → (p3 ∧ (p1 ∨ (((p1 → p1) ∧ (False → p3)) ∧ p1)))) ∨ (((True ∨ (True ∧ p5)) → p1) → ((False ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (True ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56783286980101143034727772464 : ((((p3 ∧ p4) → p1) ∧ (((p3 ∧ p3) ∧ (((((p1 ∧ ((False ∨ True) → (True ∧ (p5 ∧ p4)))) ∧ p2) ∧ p3) → p3) → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208417317175841650301178108463 : (((p2 ∨ p1) ∨ ((p4 ∨ p5) ∧ p4)) → ((((p4 ∨ p4) ∨ False) ∨ p4) ∨ ((p2 ∨ (p5 ∨ (p1 ∨ ((p3 ∨ p4) ∧ True)))) ∧ (False → p2)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746835800928189303215286891496 : ((((p3 ∨ p5) → (p5 ∧ (((((((p2 ∨ (p2 ∧ p3)) ∧ p2) ∧ (p3 ∧ p5)) ∨ False) → (p4 ∨ (p3 ∨ p1))) ∧ (p3 ∧ False)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633257434463004554839410755813 : (((((p4 → (((p3 ∨ (True → (((((p1 ∨ True) ∨ False) → (p4 ∨ p4)) ∨ p4) → True))) ∨ (p1 → p3)) ∧ p5)) ∧ (True ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254344797077514010455035332835 : ((p2 ∧ p4) → ((True → (p1 ∧ ((p1 ∨ (((p3 → (p4 ∨ False)) ∧ p5) → ((p5 ∧ ((p4 → p3) → True)) ∧ p3))) ∧ False))) → (False ∧ p5))) := by
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
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760594193794204076912534244301 : (((p2 ∧ (p3 ∧ (p1 → (((False ∨ ((p5 ∧ p3) ∨ p5)) ∨ (True ∨ ((p1 ∧ (((False ∧ False) ∨ p1) → p1)) ∧ p2))) → (False ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117557327892631682784513708861 : ((p2 ∧ ((((True → p3) ∧ (False ∨ ((p5 ∧ p1) → p4))) → p2) → (((False → p1) → (p1 ∨ False)) ∧ ((p5 ∨ p1) ∧ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65272566917259417273315285402 : ((p3 ∨ ((p2 → (p3 ∧ (((p5 ∨ ((False ∧ (p2 → p2)) → ((p5 ∧ (True → (False ∨ p4))) ∨ (p4 ∧ True)))) ∨ p2) → p4))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110763098048934351812737877070 : ((((p3 ∨ (((((True ∧ p3) ∨ (p5 ∨ p4)) ∨ (p5 → False)) → False) ∨ (p5 ∨ (((True ∨ p2) ∨ p5) → p5)))) ∧ p5) ∧ p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164710133317133253545463397313 : ((((True → ((((p5 ∧ (p5 ∨ p2)) ∨ (p1 ∧ (p5 ∧ p5))) ∨ False) ∨ p2)) ∨ p5) ∨ p3) ∨ (True ∧ (p4 → (True ∨ ((p3 ∧ False) → p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305005724342033919871908963291 : (p1 ∨ ((((p4 ∨ ((p5 → False) → (p2 ∧ False))) → (p4 ∨ (p4 ∧ p3))) → (((False ∨ (p5 ∧ False)) ∨ p2) → p2)) ∨ (False → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66460416289030509390205964935 : ((True → ((False ∧ (((p3 ∧ ((False → ((((False ∧ p4) ∨ False) ∧ False) ∨ p4)) → (False ∧ ((p4 ∧ p2) → True)))) ∧ p2) ∨ p5)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40467450048956728954923079712 : ((((((p2 → p3) → p3) ∨ (((((((p4 → True) → p5) → False) ∧ (((p2 ∧ p3) ∧ p2) ∨ p4)) ∨ p5) → p1) ∨ True)) ∨ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309809353778570557970928771857 : (p2 ∨ (((True ∨ p5) → ((p1 → ((False ∨ p1) ∨ ((True ∨ True) ∨ ((p3 ∧ p1) → (p5 → p4))))) → p3)) ∨ (False ∨ ((False ∨ p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53062475182529407368278734236 : (((True ∧ ((((p4 ∨ p4) ∧ p3) ∨ False) ∧ ((p5 ∨ True) → p4))) ∧ (p5 ∧ (True ∧ ((p4 → (p5 → ((p2 ∧ False) ∧ p1))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16616405643747287148781261062 : ((((((((((False ∨ (True ∧ p4)) ∨ False) → False) → True) → p5) ∨ False) ∧ (True ∧ ((p3 → True) ∧ p2))) ∨ p3) ∨ ((True ∨ p5) ∨ False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_245294031223481438852656183989 : ((p2 ∧ p2) ∨ (((p5 ∨ (p3 ∨ p5)) ∨ (True → ((p5 → (((p1 ∧ ((True → (False ∧ p3)) ∧ True)) ∧ p3) ∨ p5)) → True))) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354685518219362694892243162993 : (p5 → (((p4 ∨ ((p2 ∧ (p5 → ((False ∨ (p4 ∨ p4)) → ((True ∨ p5) → p1)))) ∨ (p4 ∧ ((p2 ∧ p4) ∧ True)))) ∧ (False ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308503203651173473453833814914 : (p2 ∨ ((((((p4 ∨ p5) ∨ True) ∧ ((((p3 → False) ∧ True) → p4) → p1)) ∧ ((p4 → p4) → p3)) ∨ (p2 → (False ∨ (p2 ∧ p2)))) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52876871407775467530144886452 : (((p5 ∧ (False ∨ ((False ∨ (p2 ∨ p4)) → (((p5 → p3) ∨ p3) ∧ p1)))) → ((False ∨ (p3 ∨ p3)) ∨ ((p4 → (p5 → p5)) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346279641902510239888308569051 : (p3 → ((p5 → (p1 ∨ (((p5 ∧ ((False → ((True → p3) ∧ False)) → p1)) ∧ (p4 ∨ (p2 ∨ p1))) ∨ ((False → False) ∨ p1)))) ∧ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2279293455517260514129960414 : ((((p2 → ((((True ∧ p3) ∧ True) ∧ p4) ∨ p1)) ∨ p5) ∨ (p1 ∧ p5)) ∨ (p1 ∨ ((((True ∧ (p5 ∧ p4)) → p2) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241856241165222260704209149354 : ((p1 → p1) ∧ ((p4 ∨ p2) → ((((p3 ∨ p2) ∧ p3) ∨ (True ∨ ((((p3 → True) ∨ p5) ∨ (p4 ∨ ((p1 → False) ∨ p1))) ∨ True))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_519946690651953979897834496922 : ((((p2 ∨ p3) → ((False → p5) ∧ ((p4 ∧ False) ∨ ((((((p5 ∨ p4) ∧ True) → (p3 → p5)) → p5) ∨ ((p3 → False) → p2)) ∨ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177886472904236311533183993949 : ((((p1 ∧ (((p4 → p5) ∨ p5) ∧ ((p5 → p2) ∨ p2))) → p3) ∨ p3) ∨ ((False ∧ ((True → p1) ∧ False)) ∨ (p3 → ((True → p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346371774293737646057805075853 : (p3 → ((p3 ∧ ((p4 ∨ ((((False ∨ False) ∨ ((p1 → (p5 ∨ (True → p1))) ∨ p2)) ∧ (p1 ∨ p5)) → False)) → (p2 ∨ p5))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69055537570655546408331460656 : ((p5 → ((p2 ∨ (p1 ∨ ((((((p5 ∨ True) → ((p2 ∨ p2) ∨ p1)) → True) ∧ (p5 → p4)) → (False ∧ p4)) ∨ (p1 ∨ False)))) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346182244944599688815054588098 : (p3 → (((p2 ∨ (((((((p1 ∨ p5) ∨ (p1 ∧ (p2 ∧ p3))) → (False → p5)) ∧ p4) → (True ∧ p3)) → p1) → False)) ∨ True) ∧ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47098479537552374669031300954 : ((((((p2 ∧ ((p2 ∨ p1) → p5)) ∧ ((p1 ∨ (p3 → p5)) ∧ (p5 ∨ (p2 ∧ False)))) ∨ False) ∧ ((p3 ∨ p3) ∨ p2)) ∨ (False ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172123324368639074439993743808 : ((((True → (p2 ∨ ((p4 → (False ∨ p5)) ∧ True))) → p5) ∧ (False ∨ (True → p5))) ∨ ((p2 → (((True → False) ∨ (False ∧ p3)) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690253103815466838313550517627 : ((((True → (((p2 ∨ p1) ∨ ((p4 → True) ∧ p4)) ∨ (p2 ∧ (False → (True ∨ p4))))) ∨ ((((p5 ∨ True) ∧ p5) ∨ p5) ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715888564402581841651113174 : ((((((p2 ∨ True) ∨ p3) ∧ p4) → (p5 ∨ p1)) → ((p3 → (p1 ∨ (p5 ∧ (p1 → p3)))) → (((p5 → p3) ∧ True) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136711846518573487395596491444 : (((p2 ∧ p4) ∧ (((False ∧ (True → p4)) ∧ (True → (((True ∨ (True ∧ p3)) → True) → (False → p4)))) ∨ (p1 → p4))) ∨ (True ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112876662585393794856501468904 : ((((p5 ∨ (p2 → p3)) → (p5 → ((p3 → ((p1 ∧ p5) → p4)) ∨ (True ∨ (p1 → (p2 → ((p2 ∧ p4) ∨ p2))))))) → False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191013599266980084549067636580 : (((p4 ∨ ((False ∧ False) ∨ p3)) ∨ (p5 ∧ (True ∧ False))) ∨ (True ∨ (((((p5 ∧ p5) → (p3 ∨ True)) ∨ (True ∨ (p3 ∧ True))) ∧ p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192158863106796021849835947771 : (((((p3 ∧ (p2 ∧ p1)) ∨ (p1 ∨ True)) ∧ True) ∧ p2) → ((False ∨ p5) ∨ ((p1 → p5) ∨ (((p5 → (p1 → p5)) ∨ True) ∨ (p4 → False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
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
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
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
    case inr h13 =>
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
theorem thm_5_vars_171518802364925914210810740214 : ((((p5 ∧ ((((p4 ∧ p5) ∧ p1) ∧ (p3 → p5)) ∧ (p4 ∧ p4))) ∧ False) ∨ p5) ∨ (((p3 → ((p2 ∨ p3) → p2)) ∧ True) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159009433342086662073884364131 : ((p4 ∨ ((p5 → ((False ∧ (p5 ∧ (False ∧ ((p4 ∨ ((p2 ∧ p2) ∨ True)) ∧ p1)))) ∨ p1)) ∨ p5)) ∨ ((True → True) ∨ (False ∧ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142546340434418988623628593563 : ((True ∨ ((p2 ∨ p2) ∧ (((((p2 → (((True → (p2 ∨ p5)) ∧ p3) → False)) → (p3 ∧ False)) ∨ p3) ∨ True) ∧ True))) → ((p5 ∨ p4) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
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
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45973522457549991289224771294 : (((((((p5 ∨ (False ∨ (True ∧ ((p1 ∧ p3) ∨ True)))) ∨ (True ∧ ((p1 → p1) → (p2 ∨ p5)))) ∧ p3) ∧ True) ∧ p3) ∧ (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325900392145536688156736263166 : (p5 ∨ (p4 ∨ (p2 ∨ (p3 → ((p3 ∧ (((False ∧ p5) ∨ (p3 → ((p2 ∨ (True ∧ p4)) ∨ p2))) → False)) → (((p4 ∨ p5) ∧ True) ∨ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



