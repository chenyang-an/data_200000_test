variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172932828753522629377698761220 : ((p3 ∧ ((p4 ∧ (p3 ∨ (((((p1 ∨ p1) → p1) → p3) ∨ p4) ∧ p1))) → p3)) ∨ ((((p1 ∧ ((p4 → p4) → p4)) → False) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119105084859087077858798545702 : ((p1 → (((p5 → True) ∧ p5) ∨ (((False ∧ ((False ∨ (p3 ∧ (False ∨ False))) ∨ (True ∨ p3))) ∨ (True → (p4 → p1))) ∨ p2))) ∨ (p2 → False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204364700690710832103606475730 : (((p2 ∨ (p2 ∨ (p1 ∧ p5))) ∧ p5) ∨ (((False ∨ p1) ∨ ((True ∨ p5) → (False → (p4 → (((p2 → p2) ∧ True) → p2))))) ∧ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45647501167757460256255290985 : (((p4 ∨ (True ∧ ((p2 ∧ (((p1 ∧ (False → p1)) → (p4 ∨ p3)) ∨ ((p4 → p5) → True))) → (True → (p1 → (True ∨ p5)))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665966269386426516064646031733 : (((((True ∧ (True ∨ (p1 → (((p4 → p3) → (p1 ∧ False)) → ((True ∧ p5) ∧ (p3 ∨ (p4 → p2))))))) → False) ∧ (p5 ∧ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186684536288548217421543366497 : (((p4 ∨ (p3 ∨ (True ∧ (p4 → p5)))) ∧ ((p4 → p4) → p1)) → (p5 ∨ (((p2 → True) → (p4 → ((True ∨ (p3 → p2)) → True))) ∨ p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52655535916739660074923288010 : (((p2 ∧ (((p5 → (p4 ∨ (p3 ∨ p1))) ∨ ((p4 ∨ p3) → False)) ∧ False)) ∨ ((((p5 ∧ p2) ∨ True) ∨ (p1 ∧ (p2 ∨ p1))) ∨ p5)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318906161921634699483055688934 : (p4 ∨ ((p1 → ((False → p3) ∧ ((False → (p1 ∨ ((((p1 ∧ p5) ∧ p1) ∨ p2) → p4))) → (p5 ∧ (p1 ∨ p2))))) ∨ ((True → p5) → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662839227228223103395561894138 : (((((True ∧ (p1 ∨ False)) ∧ ((False → ((p1 → (((p1 ∧ p2) → p5) → (p3 ∨ (p1 → (p5 ∨ p3))))) ∧ p5)) ∧ True)) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806207598893757858313852822577 : (((p4 → ((((p3 ∧ True) → (False ∨ (p3 → (p1 ∨ (p5 ∧ (p2 → (((p3 → p3) → (p4 → p1)) → (p2 ∨ p2)))))))) → False) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648676214729712216934258402667 : ((((((p1 ∧ p5) ∨ ((p5 ∧ (p1 → p4)) ∨ (p3 ∧ (True ∧ (((p3 → (False ∨ (p2 ∧ p2))) → False) ∧ True))))) ∨ p1) ∧ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53277440161750311425768946446 : (((p2 ∧ (p1 ∨ (((p4 ∧ (p4 ∧ p5)) ∧ True) ∨ (p1 → True)))) ∨ (((True ∨ False) ∧ False) ∨ (((p3 ∨ p3) → p3) ∧ (p4 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62494047919164430741304350260 : ((p3 ∧ (False ∧ ((p3 ∨ (((True → p1) ∧ ((p5 ∨ (p2 ∧ p5)) ∧ p3)) ∨ (p5 ∧ ((((p4 → p1) ∧ p4) ∧ p2) ∨ True)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225740309265117006610845430388 : (((p4 → p2) ∧ p5) ∨ ((((((p5 ∨ (((p4 ∧ p3) ∨ False) → False)) ∧ (((p1 ∨ True) ∧ (p2 ∧ p1)) ∧ False)) → p2) ∧ True) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596445599241587310935674101196 : (((((p3 → (((p1 → (p2 ∧ p1)) ∧ False) ∧ p4)) ∨ (True ∧ (p3 ∧ (p5 ∨ (((p4 → p1) ∧ (True → p2)) ∧ (p2 → p1)))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309409798387899173604222711430 : (p2 ∨ ((p3 → ((p5 ∨ (p1 → (p3 ∨ p2))) → (p4 ∨ (((p3 → (p2 → p3)) ∧ p1) ∨ (p2 ∨ (p1 ∨ (p5 ∨ p3))))))) ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326836213031596905905612906450 : (True → (((((p3 → (((p5 ∨ p4) ∨ True) ∨ ((p3 ∨ (p5 → (p4 ∨ False))) ∨ p4))) ∧ p2) → ((p4 ∨ p4) ∧ (p3 → False))) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335882124204969567591302106681 : (p1 → (((p3 → (((p1 → p3) ∨ True) ∧ p2)) → ((True → (p4 ∨ ((p4 ∧ p4) ∨ p4))) → (p1 ∧ ((p1 → p5) ∨ (False → p4))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168576170368951463660365872274 : ((p2 ∧ ((True → ((False → ((False ∧ p1) → True)) ∧ ((True ∨ p2) ∧ p1))) ∧ (p5 → p4))) → ((p2 → True) → (((p3 → False) → p2) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662783029963590751340184883943 : (((((p3 ∨ ((True → False) ∨ p1)) → ((p3 ∨ True) ∨ ((False → (((p5 ∧ p1) → True) ∨ p3)) ∧ ((False ∧ False) ∨ p3)))) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225064985398494113622246645150 : (((p1 ∧ p1) ∧ p4) ∨ (((p1 ∧ ((p1 ∨ p3) ∧ ((p5 → ((p4 → False) ∧ (p3 ∨ p4))) → p5))) ∧ p5) → ((True ∧ p2) ∨ (False → p1)))) := by
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
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299255376774093853387146824161 : (False ∨ (((p5 → ((p3 ∧ (p2 → False)) ∨ ((True ∨ (p2 → p5)) ∨ (((p5 ∨ p1) → True) ∧ False)))) ∧ ((p5 ∧ p2) ∨ (p5 ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218367083972685477132076080126 : (((p3 → p4) ∨ (p2 → p5)) → ((p3 → ((p1 ∧ ((((True ∨ p3) ∧ p1) → p2) ∨ False)) ∨ (False ∨ p5))) ∨ (p3 ∨ (True ∨ (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614285837107833402394519655249 : ((((((True → ((p4 ∧ ((p2 ∧ p4) ∨ False)) ∧ p4)) ∨ ((p5 ∨ (p2 → p5)) ∧ (p2 ∨ (False → False)))) → (p2 ∨ (p5 ∨ True))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192688910513165648958598431203 : (((((True ∧ (p5 ∧ False)) ∨ p4) ∨ (True ∧ p5)) → p3) → (((p4 ∨ p2) → p3) ∨ (True ∨ (p5 ∨ (((p5 ∧ True) ∧ p1) → (p5 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197759962815674522575657687326 : (((p5 ∧ (p5 → p3)) ∧ (p1 ∧ (p1 → p4))) ∨ (((((False ∧ True) → (False ∨ p4)) ∧ p5) → False) ∨ ((p5 ∧ False) → ((False ∧ p1) ∨ p4)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200674091635651341453788365542 : ((p1 ∧ (p1 ∨ (((p3 ∨ p4) → True) ∨ True))) → (p5 → (((((True → p1) → (True → ((p2 ∨ p5) → p1))) ∧ p2) → (p3 ∧ p1)) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59351874454028572428306661163 : (((p5 ∨ p1) ∨ ((((p5 ∨ (p5 ∨ p4)) → (p3 → (p4 ∨ (p2 ∧ ((p3 ∨ p2) ∨ p5))))) ∨ (p4 → p2)) ∨ ((True → p1) → True))) ∨ p5) := by
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
theorem thm_5_vars_244508152147659000160926648312 : ((False ∧ p3) ∨ (((p2 ∧ (False ∧ p3)) ∨ (False → ((((p2 ∨ p5) ∨ (p1 ∧ p1)) ∨ False) ∨ ((p5 ∨ p3) → True)))) ∨ ((False ∧ p4) → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114712969822048179631555723170 : ((((((p4 → (True ∨ p3)) → p3) ∨ (p1 → (((False → p1) ∨ p2) → p3))) → True) → (p3 ∨ (True → (p4 ∧ (p3 ∧ p1))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761049361600896919038423878138 : (((p2 ∧ (p1 → ((p1 ∧ (((p3 → (p4 ∨ False)) ∨ p2) ∨ (p2 ∨ p4))) ∨ ((p1 ∨ (p2 ∨ p4)) ∧ (((p4 ∧ p4) → True) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64775269816185049895183170074 : ((p2 ∨ ((((((False → p2) ∧ ((p1 → (p2 ∧ (True ∨ (p2 ∧ (p2 ∨ True))))) ∨ p5)) ∧ (True ∧ p5)) ∨ (p3 ∨ True)) ∨ False) ∨ p4)) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193752269293317582588965259814 : ((p3 ∧ (((p3 ∨ (p4 ∧ True)) → p2) → (p3 ∨ p5))) → ((((p5 → p4) → (p3 ∧ (p4 ∧ (p2 ∨ (True ∨ False))))) ∧ p1) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191575844834567029121887889568 : ((p2 ∧ ((((False ∨ False) → p2) ∧ p1) ∨ (p1 ∨ p5))) ∨ ((p5 ∨ (p1 ∧ p4)) ∨ (False → ((True ∨ (p3 → ((False ∧ p2) ∨ p5))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174557029153590168799599066072 : ((((p5 → (p5 ∧ True)) ∨ p2) ∧ (p5 ∧ ((p1 ∨ (p1 ∧ False)) → (True ∨ True)))) → (((p1 ∧ (p5 → p2)) ∧ p1) → (p5 ∧ (True → p2)))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h8.left
    let h14 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h25 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h26 := h19 h25
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h21.left
    let h29 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652590095354313064785589404155 : ((((False ∨ (((((p4 ∨ True) ∧ p3) ∨ p4) ∧ (p5 → (((False ∧ p3) ∨ (p3 → False)) ∧ p3))) → (p5 ∧ (p1 ∧ p5)))) ∧ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150851493171787692066248134641 : ((((((True ∨ ((p4 ∨ True) ∧ (p2 ∨ p5))) → p1) ∧ p4) ∨ ((True → False) ∧ (p1 ∧ (False ∨ p1)))) ∨ True) → ((p2 ∨ (True ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783709320675938044790108275275 : (((p3 ∨ (((False ∧ (p1 ∨ False)) ∧ (True → p1)) ∨ (True ∨ (((False → p1) → p1) ∧ (((p2 → p1) ∧ False) ∨ (p1 ∨ (p2 → p4))))))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50894611061783362625123137752 : ((((p1 ∨ (p5 ∨ (((p5 ∨ ((p3 ∨ False) ∨ (p4 ∧ p5))) → (True ∧ p5)) → p1))) → p1) ∧ ((p1 ∧ p1) ∨ (p1 ∨ (p4 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593179558555031312558846866994 : (((((((p3 ∧ p1) ∧ p5) ∨ (False ∨ ((((p4 ∨ (p3 ∨ True)) → p1) → False) ∨ (True → (p1 → p5))))) ∨ ((True ∨ p5) ∧ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628082734261692605414352723617 : (((((((False → True) ∧ (p1 ∨ False)) → ((p1 → (((p1 → ((p1 ∨ p2) ∧ (p5 ∧ p5))) → True) ∨ False)) ∧ (p1 → p3))) ∧ p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50413526968685813883037533446 : (((p1 ∧ ((p1 ∧ ((p3 ∨ (p2 ∨ p3)) ∨ False)) ∨ ((p5 ∨ (False → p4)) ∨ ((p3 ∧ p3) → p2)))) ∨ (((p5 ∨ p1) ∨ p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325736777190292444998494016733 : (p5 ∨ (p2 ∨ ((p3 ∨ ((((True ∨ ((True ∨ ((p4 ∧ p1) ∧ (False ∨ False))) ∧ p1)) → False) ∨ ((p1 ∨ p5) ∨ (p5 ∨ p4))) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187472022987371887363408705888 : ((True ∨ (p3 → ((((p3 ∧ False) ∨ (True → p3)) ∧ p5) ∨ p3))) → (((p2 → ((p4 ∨ (p3 ∨ p4)) ∨ True)) ∧ ((p2 ∧ True) → True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143306344407379208829864684335 : ((p4 → ((((((p1 → p2) ∨ p4) ∧ p5) → p5) ∧ (p3 → ((p4 → p5) → (((p5 → False) ∨ p1) → True)))) ∨ p2)) → (True ∧ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52566680921772244731080959072 : (((((p3 ∨ p2) → ((p1 ∨ p3) ∧ ((p3 ∧ p3) ∨ p3))) ∧ (p3 ∨ p4)) ∨ ((p5 ∧ ((p5 ∨ p3) ∨ p2)) → ((False → False) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_118225637612238839627257273646 : ((p1 ∨ ((p3 ∧ (((p5 ∧ ((((p2 → ((p4 ∧ p1) ∨ False)) ∧ ((False → False) ∨ p3)) → p4) ∨ p3)) → False) → p1)) ∨ p3)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300666584009860267057449792543 : (False ∨ (((((((p1 ∨ False) ∨ True) → (p3 → False)) ∨ (p5 ∧ p1)) ∨ ((p4 ∧ p3) ∨ p3)) ∨ True) ∨ (p4 → (False ∨ (p4 ∧ (p5 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64436406368642252183803274069 : ((p1 ∨ ((((((((p4 ∧ True) → p4) ∨ (((p3 ∧ p5) → (p4 ∧ False)) → False)) ∧ p3) → p2) ∧ (p2 ∧ p1)) ∨ p1) ∨ (p5 → True))) ∨ p1) := by
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
theorem thm_5_vars_118525953225603445122226293440 : ((p3 ∨ ((p4 ∨ True) → (((p4 ∨ ((p1 ∧ p2) ∧ p3)) ∨ p5) ∨ ((p3 ∨ p2) → (p5 ∨ (((False ∧ False) ∧ p3) → p4)))))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751233101232479738934186269207 : (((True ∧ ((p5 ∨ (p4 ∧ p5)) → ((p1 ∧ True) ∧ (False ∨ (((p2 ∧ True) → ((((True ∨ False) → True) ∨ True) → (False ∨ p3))) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587323237146938188138240104610 : ((((((((p3 ∧ p5) ∨ False) ∨ (False ∧ (p1 ∨ (p3 → ((p2 → p5) ∧ (p3 → (((p4 ∧ p2) ∧ p1) → p5))))))) ∧ p2) ∨ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157787917513736702977777575965 : (((((p5 ∧ (p1 → p2)) → p5) → (((p2 → False) ∧ p2) → False)) ∨ ((True → p1) ∨ (p5 → p3))) ∨ ((p3 ∧ p3) ∧ (p1 ∨ (True ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181171567849036163521883644816 : ((p1 ∧ ((((True → (True → p3)) ∧ p5) ∧ (p3 → (p1 ∧ p5))) → p1)) → (p3 → (p3 ∧ (False → (False ∨ (p5 ∨ (p4 ∨ (p1 → p1)))))))) := by
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47443506965913372011908937393 : (((p3 ∧ ((True ∨ (((False ∨ (p1 → p2)) ∧ ((True ∨ (p4 ∨ p4)) ∨ p1)) ∧ (False → p3))) → ((p3 ∨ p3) ∨ True))) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50196922586063788442224239412 : ((((True → (((False ∧ p1) ∨ (p4 ∧ (True ∨ (((p1 ∧ (True ∨ True)) ∨ p2) ∧ p4)))) ∨ p3)) ∧ False) ∨ ((False ∧ (True ∨ p5)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860033751413951745026312276836 : ((((((False ∨ (((True → (p2 → p3)) ∨ (((False ∧ p3) ∧ p4) ∧ p2)) ∧ p1)) ∨ ((p4 → p3) ∨ (False ∨ True))) ∨ (False → p3)) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ (((True → (p2 → p3)) ∨ (((False ∧ p3) ∧ p4) ∧ p2)) ∧ p1)) ∨ ((p4 → p3) ∨ (False ∨ True))) ∨ (False → p3)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_532640391093472177454828000 : ((((p5 ∧ (((p1 ∧ p4) ∧ (((p5 ∨ (p4 ∧ p1)) → p4) → (True ∧ True))) ∧ ((p2 ∨ (p4 → False)) ∨ p3))) ∨ p3) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158737151136852391947067860958 : ((p3 ∧ (True → (((p1 ∧ p2) ∧ (((False ∨ p2) → (False ∨ p5)) → (p5 ∧ (p2 ∧ p4)))) → p5))) ∨ ((p4 ∧ ((p5 ∧ True) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48600873145961975590718728238 : (((((p2 ∨ (True ∧ (True ∧ (p4 → (((p2 → False) ∨ p5) ∨ (p1 → p2)))))) → (p1 ∧ p4)) ∨ (p1 → p1)) ∧ (False → (True ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134135698361509823124953164288 : (((((p3 ∧ ((p1 ∧ True) ∧ p3)) → ((((p2 ∨ (False → p1)) → True) ∧ True) ∧ (p2 ∧ p1))) → (p2 ∨ p1)) ∨ p1) ∨ ((False ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149341532617950185275781096652 : (((p1 ∨ p4) → (((p2 → (p2 ∨ ((False ∨ p5) ∨ p3))) ∨ False) → ((((p1 ∨ p2) ∨ p3) → False) → p4))) ∨ ((p2 ∨ p2) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303884444965163156314371256258 : (p1 ∨ (((((((p1 → ((p5 ∧ False) ∧ False)) → False) → (p5 ∨ (False ∧ p5))) ∧ p5) → (p3 ∨ p1)) → (True → ((p5 ∧ p2) ∨ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307534952455147159650255562631 : (p1 ∨ (True → (p2 → ((p1 ∧ (((False ∨ p5) ∨ p1) ∨ p2)) ∨ ((p1 ∧ (True ∨ (((True ∧ p3) → (p5 ∧ p3)) ∧ p5))) ∨ (p3 → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306000215496423108123279552793 : (p1 ∨ (((p4 ∧ p3) ∧ (p3 ∧ p4)) ∨ ((((p1 → p5) → (p1 → p1)) ∨ ((True ∧ (p4 → False)) ∨ (p2 ∧ (p2 ∧ True)))) ∨ (p4 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214572355848988608670430643184 : (((p2 ∨ p2) ∧ (True → p3)) ∨ (((True → p4) → (((False ∧ p3) → (((p5 → False) → (True → (p1 ∧ p1))) → p1)) → False)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628859198299991006705960053150 : (((((p5 → ((((True ∨ (True → True)) ∧ (p4 ∧ p2)) ∨ ((p1 ∨ (p2 → False)) → False)) ∧ ((p1 ∨ (p1 ∨ True)) → p3))) ∧ p5) → p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118277299505277021030938771133 : ((p1 ∨ (((p5 → True) → p4) ∧ (((False → p5) ∧ (((p1 ∨ p2) ∧ (p3 ∧ ((p5 → p4) → (p5 ∨ p4)))) → p1)) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165858078859553167888954150709 : (((p4 ∧ (p4 ∧ p5)) ∨ (True → (((False → p4) ∧ False) ∨ (False ∧ ((False → p3) → p2))))) ∨ (True ∧ (True ∨ ((p3 ∧ False) ∧ (p3 ∨ p4))))) := by
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
theorem thm_5_vars_136189446763533171918337890564 : ((((True ∧ (p1 ∨ p1)) → (p1 ∨ p1)) ∧ ((p5 → ((p5 → p1) → ((True ∨ p1) ∨ ((p2 ∨ False) → p5)))) → p3)) ∨ (p3 → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119192830109395878924154865054 : ((p2 → ((p4 ∨ (False ∨ ((((p5 ∨ p3) ∧ ((False ∨ True) ∨ p3)) ∨ p2) → ((p2 ∨ (False ∨ p4)) ∨ p3)))) → (False ∨ p5))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44161643905849275206958793523 : ((((((p3 → (((False → p2) ∨ p1) ∨ p1)) ∨ ((p4 ∨ p4) ∨ False)) ∨ ((p4 ∨ False) ∧ (p1 → p2))) → ((p4 → p1) ∨ p1)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943096815098547089955841723479 : (((((p1 → p5) ∨ (p3 ∨ False)) ∧ (p5 ∧ ((((((p3 ∨ p5) ∨ (True ∧ p5)) ∨ (p2 ∨ False)) ∧ p2) ∧ (p5 ∨ (p1 → p3))) → p5))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185103429447913103930535756605 : (((p1 → False) ∨ ((p2 → (p4 ∨ (p4 ∨ p4))) ∧ (p2 ∨ False))) ∨ (False → ((((True → p5) ∧ (p4 ∧ p5)) ∧ p2) ∧ ((p5 ∧ p5) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705624768780103907408884759283 : (((((False → (p1 ∨ ((p3 → p4) → p4))) → False) ∧ (p2 ∨ (((p3 ∨ ((False → (p1 ∨ p4)) ∧ p2)) ∨ (True ∧ p5)) → (p3 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85946964628761827944158409868 : (((((p3 → (p1 ∨ (p1 ∨ (True ∨ p4)))) → True) → p4) ∧ ((p1 → ((((True ∧ p1) ∨ (p1 ∧ p4)) ∨ (False ∨ p5)) ∨ p3)) ∨ p1)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 → (p1 ∨ (p1 ∨ (True ∨ p4)))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → (p1 ∨ (p1 ∨ (True ∨ p4)))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256911816675669902174022842254 : ((p1 ∨ p4) → ((False ∧ (p1 ∨ p4)) ∨ (((((False → p1) ∨ (p2 ∧ p4)) ∧ ((False ∧ (p3 → p1)) ∨ p4)) ∨ ((p2 ∧ False) ∧ p1)) ∨ True))) := by
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
theorem thm_5_vars_637105107104624505262082658540 : ((((((((False → True) ∧ p5) → (p5 → ((p2 → p4) → True))) → p4) ∨ (p5 ∧ (p2 ∧ ((p5 ∨ (p4 ∧ p3)) ∧ (p5 ∨ p4))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336117499267679955355989015046 : (p1 → ((((((p5 ∨ p4) ∧ (False ∧ p3)) ∨ ((p4 → p2) → (p3 → ((p4 → (False ∨ p5)) ∨ (False ∧ p1))))) ∨ (p4 ∧ p5)) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166412510764546462146881053494 : ((p1 ∨ (((((p5 → (False ∧ ((p1 ∧ (p4 → False)) → False))) → False) ∨ p5) ∨ p4) → p5)) ∨ (((True → False) ∨ ((False ∨ False) ∧ p4)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111412702455966636037370877613 : (((p3 ∨ (((p3 → (((False → ((False ∨ p2) ∧ (p5 → p5))) ∨ p5) → False)) → (((p1 → p2) ∨ p1) ∨ p3)) ∧ p5)) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171357581751257961441848141599 : (((((((True ∧ (False ∧ True)) ∧ p1) ∧ False) ∨ (p1 ∧ p4)) ∧ (True ∨ True)) ∧ p3) ∨ ((((False → (p4 ∨ True)) ∨ (p5 ∧ p2)) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66189568903941362024091397871 : ((p5 ∨ ((p5 → (p4 ∨ ((((((p5 ∧ False) ∨ (p1 ∨ p5)) ∧ p5) → (p5 ∨ True)) ∨ p3) ∧ p2))) → ((p3 → p4) → (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110869867716487825133908083860 : ((((((p5 → p3) → (((p3 ∨ (((((False → False) ∨ (p2 ∨ p3)) ∧ False) ∨ p3) → p4)) ∨ False) ∨ True)) → True) → False) ∧ p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197251259408382216201187699463 : ((((p2 ∧ (True ∧ (p5 ∧ p4))) → p1) → p4) ∨ ((p3 ∧ p2) → (((False ∧ True) → False) ∨ ((p2 ∨ (False → ((p4 ∧ True) ∨ p3))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64068981269917458295594913327 : ((False ∨ ((((p5 ∧ p5) ∧ (p5 ∨ (((p2 ∨ (p4 ∧ p3)) ∧ p4) → True))) → (True → p2)) ∨ ((p2 ∧ ((p5 ∧ p1) → p5)) → p2))) ∨ p1) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47283644676529347955530111087 : ((((((p3 ∨ p3) → p3) ∧ True) → ((((True ∧ p4) → (False ∧ p4)) ∧ p5) ∨ (p3 → ((True ∧ (p3 ∨ p5)) ∧ p2)))) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41378801763198225841893314930 : ((((p3 → ((False ∧ (p1 → (True ∨ (p3 ∧ (p1 ∧ p1))))) ∧ ((True ∧ p4) ∨ False))) → (p2 → (((p1 ∧ True) ∨ p4) ∨ p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56344233830616101004927411560 : (((((p3 ∧ p3) → p5) ∨ p4) → ((((p1 ∨ (p1 ∨ p4)) → p4) → p1) ∧ (p4 → (((False → (True ∧ p3)) ∨ (p4 → p4)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32986456266118456037507232704 : ((p3 ∨ ((((((p5 → p5) → (p1 ∧ p5)) → p3) ∨ (True ∧ (p4 → p2))) ∨ (True ∧ False)) → (((p2 ∧ True) ∧ (p3 ∨ p4)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95631002710827099495045766695 : ((p5 ∧ (((p3 ∧ ((p3 ∨ p3) ∨ False)) ∨ True) → ((True → True) ∧ ((False ∧ (((p3 → p2) → p5) → (p1 ∧ (p1 ∧ p5)))) ∧ p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ ((p3 ∨ p3) ∨ False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41222860169331793138128158929 : (((((((((p2 ∨ ((p3 → p2) ∨ False)) ∨ False) ∨ p2) → p3) → p2) ∨ (False ∨ (False ∨ p1))) ∧ ((p2 ∨ False) → (p3 → p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175330065889723218963801273704 : ((p4 ∨ (p4 ∧ ((p2 ∨ (p1 → (((False ∧ (False ∧ p2)) ∨ True) → True))) → p4))) → ((((p3 ∧ (p5 ∧ p2)) ∨ (p4 → True)) ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40043852248782866755579577838 : (((((p2 ∨ (p3 ∧ ((p5 ∨ ((p1 ∨ (p3 → ((((p5 ∨ p2) ∧ (True ∨ p1)) ∧ False) ∧ p4))) ∨ p3)) ∧ p3))) ∧ p1) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149131555022295739561831999783 : (((p3 ∧ p3) ∧ (((p1 ∧ True) ∨ (False ∧ (((((True ∧ (p1 ∨ p5)) → True) ∧ p4) ∨ p4) ∨ p2))) ∨ True)) ∨ (p1 ∨ (p3 ∨ (False → p2)))) := by
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
theorem thm_5_vars_319549991896607518633650293626 : (p4 ∨ (((p5 ∨ (p2 → p5)) ∨ (p2 ∨ (p1 → (p3 ∨ p1)))) ∨ ((p2 ∧ (((p2 → ((p5 ∨ p2) → (False ∨ p3))) ∧ p4) ∧ True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324199374140219117552439722903 : (p5 ∨ (((p5 → ((p4 ∧ p2) ∨ (False ∧ p1))) → (p3 ∨ False)) → (p1 → ((p5 ∧ p1) → ((((p4 → p1) ∧ p3) → (True → p4)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164903215147011018628730360236 : ((((((((False ∨ p1) → p4) ∧ ((False → False) ∧ p5)) → p5) → (p4 → p4)) ∧ p5) → p3) ∨ (True ∨ (((True ∨ p1) → (True ∨ p2)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102864816477925477340108177664 : ((((p1 ∧ (False ∧ ((False ∨ p1) ∧ ((((True ∧ (p2 ∨ p1)) → ((p5 ∧ p4) → p5)) ∧ p3) → p2)))) ∨ (True ∨ False)) ∨ True) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205582992693970767254341706226 : (((p2 → p1) ∧ ((False ∧ p4) ∨ p5)) ∨ ((((((False ∨ p4) → p4) ∨ p1) ∧ (p4 ∨ (p3 → p3))) → (p1 → True)) → (p1 ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



