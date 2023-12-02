variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706799297611680053672439564177 : ((((((p3 ∧ p1) ∨ (p3 ∧ (p1 ∧ True))) ∧ p1) ∨ (p4 ∧ (p5 ∨ (((p5 ∨ (((True → p3) → (p1 ∧ True)) → p3)) → p1) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147095912944494882888503793301 : ((((p5 ∨ (p4 → False)) ∧ ((((p1 ∧ p4) ∨ (((True ∧ True) ∧ (False → p4)) ∧ p3)) ∧ p1) ∨ False)) ∧ p4) ∨ ((p1 ∧ (p2 → p1)) → p1)) := by
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
theorem thm_5_vars_206461348684930314663333238423 : ((p4 ∨ (p4 ∧ (True ∨ (p3 → True)))) ∨ (p2 ∨ (((p1 ∧ ((p4 ∨ (False → p4)) ∨ (p5 ∧ (p4 ∨ p5)))) ∨ (p2 ∨ p1)) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_174282103982852217779665303439 : (((p2 ∧ ((((p1 → True) ∧ False) ∧ False) → (False ∧ p5))) ∧ ((p4 ∨ p5) ∨ p5)) → (((p5 → (p2 → True)) ∨ p5) ∧ ((True → p4) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317608837033256050363521840470 : (p4 ∨ (((p5 ∨ ((p3 ∨ p5) → (p4 ∧ ((p3 → (((False ∧ p3) ∧ p2) ∨ (True ∨ p5))) ∧ (False ∧ ((p3 → p1) → False)))))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115062663040987042061785651907 : ((((True ∧ (p2 → (p1 → (p5 ∨ p5)))) → ((p5 ∨ False) ∨ False)) ∨ (((p3 → ((p2 ∧ True) ∨ p1)) ∨ (False → p4)) ∨ p3)) ∨ (p2 ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696580019556647765993225669128 : (((((((((p5 ∧ p3) ∨ p1) ∧ (p2 ∧ p1)) ∨ p4) → p3) ∨ p5) ∧ (p4 ∧ (((False → ((p1 ∨ p5) ∨ p3)) ∨ (p4 ∧ p3)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347751321883942632005288458699 : (p3 → (((p5 ∧ p5) ∧ p2) ∨ (((p3 → (((True ∨ p5) ∨ p2) → (p2 → ((p3 → (p3 ∧ (p1 ∧ p1))) ∧ False)))) ∨ (p5 → p5)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177991177407435709687466582220 : (((p5 ∧ ((p5 → p2) → (True ∧ ((p1 → (p5 → p2)) ∧ p4)))) ∨ p4) ∨ ((p5 ∧ (p1 ∨ (((False ∨ True) → p5) ∨ (p5 ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635466730056793269254552624510 : (((((True → (False ∧ ((p3 ∨ (p1 → p4)) → ((True ∧ (p3 ∧ True)) → (True → (False ∨ False)))))) ∧ (p3 → (True ∨ (False → p5)))) → p1) ∨ p1) ∧ True) := by
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
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782459477182590837282678027737 : (((p3 ∨ (((p2 ∧ ((p4 ∧ p3) → ((p3 → (p4 → (p3 → False))) ∧ (True ∨ p1)))) → (p5 → (((True ∧ p5) ∨ p4) → p4))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_191346986630048701036879875048 : (((False ∨ p5) ∨ ((p4 ∧ (p3 ∨ False)) ∨ (p3 → True))) ∨ ((((p5 ∧ (True ∧ ((p3 ∨ (p5 ∧ (True ∨ True))) → p4))) ∧ p2) ∧ p4) → p5)) := by
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
theorem thm_5_vars_345959107180019198184509266845 : (p3 → ((((((p4 ∨ p2) → p3) ∨ (False ∧ p4)) → p5) ∧ (p1 → (p1 ∨ (((p2 ∨ (p3 ∨ True)) ∨ (p2 → (p1 ∨ p2))) ∨ p1)))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p4 ∨ p2) → p3) ∨ (False ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166571274733326469623359665267 : ((True → ((((((p2 → (False ∨ False)) → p2) ∧ ((p1 → p2) ∧ p5)) ∧ True) ∧ p1) ∨ p3)) ∨ (False → ((p5 ∨ True) ∨ (p3 ∨ (p2 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777266352186542604204094647756 : (((p1 ∨ (((p3 ∨ ((p4 ∨ (((p1 → p1) ∨ (False ∨ (p4 ∨ p3))) → (p4 → p3))) ∧ p1)) → (p2 ∨ p4)) → ((p4 ∨ p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314931852826496970826007118088 : (p3 ∨ ((False ∧ (p3 ∨ ((True ∨ ((p4 ∨ p1) ∧ p5)) → p4))) ∨ (False → ((p2 → (p4 ∨ ((p4 ∧ p2) ∧ p3))) ∨ ((p3 → p5) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323489271622220253968534520245 : (p5 ∨ ((((((p1 ∨ (p1 → (True → (False → False)))) ∨ (False ∧ p2)) → ((p4 ∧ False) → p4)) ∧ p3) → (True ∧ p2)) ∨ (False → (p5 → p1)))) := by
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
theorem thm_5_vars_198419427663026925958677499595 : ((p4 ∧ ((True ∧ (p1 ∧ p1)) → (p5 → p1))) ∨ (((p1 → p2) → p1) ∨ (((p2 → False) ∧ ((p1 ∨ p4) → True)) ∨ ((True ∧ p1) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303912893779046429511934565314 : (p1 ∨ (((p1 ∧ ((p4 → ((False ∧ p1) ∨ (p3 ∨ (False → p2)))) → p2)) ∨ ((True ∨ (p4 ∨ ((p4 → (p4 ∧ False)) ∧ False))) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173131129043043043810705767173 : ((p2 ∨ (p5 ∨ ((p3 ∨ (p4 ∧ (((p1 → p3) ∧ p1) ∧ (p4 ∨ p4)))) ∧ True))) ∨ (p2 ∨ (False → (False → (p4 → (True → (p4 → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255913418381700200493784120831 : ((True ∨ p2) → ((p4 → ((p5 ∨ (((p3 → (True ∧ p5)) ∨ p2) ∧ (True ∧ (((((p1 → p1) ∨ p1) ∨ p1) ∧ False) ∧ p4)))) ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706861999940709929734177479118 : (((((False → (p4 ∨ (p2 → (True ∧ p4)))) ∧ p1) ∨ ((p2 ∨ ((((p2 → False) ∧ p5) → p3) ∧ ((p2 → (p2 → p3)) → p4))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_165094299461833910451474317813 : (((p4 ∨ (((((p1 → (False ∨ p5)) ∨ (p2 ∧ p4)) ∨ p4) ∨ (True → p3)) → False)) → p1) ∨ ((p2 ∧ p2) → ((False → (p1 ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356343985863356553604007755492 : (p5 → (((((p2 → (p3 → p4)) ∧ (((p1 → p5) → p3) → p2)) → p3) ∨ p4) ∨ ((p4 ∧ (((p5 ∧ p1) ∧ p4) ∧ (p1 ∧ p3))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336367481501511679798155536799 : (p1 → (((p3 ∨ p1) → (p3 ∨ (((p3 → (((p2 → (p4 ∧ p5)) ∧ ((p1 ∨ p1) ∨ p2)) → p2)) → (p4 → p3)) ∧ (True → p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193934443538135154261386899839 : ((p2 ∨ ((((p2 ∧ p4) ∧ p5) ∧ (p1 → p2)) ∧ p5)) → (((p3 ∨ (True → p1)) → (p1 ∧ (p2 ∧ (p2 ∧ (True → (True ∨ p3)))))) ∨ p2)) := by
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
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153214894772447031856617230410 : ((True ∨ ((((p3 → p3) ∨ (p4 ∧ p4)) → p2) ∨ ((p4 ∧ (p1 ∧ ((p5 ∧ True) ∧ (p1 ∨ True)))) → p4))) → (((False ∨ True) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917235381267581515838694135672 : (((((p4 → (((p5 ∨ ((p3 → p2) ∨ (False ∧ (p2 ∧ False)))) ∧ True) ∨ p4)) ∨ False) → ((True → ((p3 ∨ (p2 ∨ p1)) → p2)) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (((p5 ∨ ((p3 → p2) ∨ (False ∧ (p2 ∧ False)))) ∧ True) ∨ p4)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136068922038608524179181049853 : (((((p2 ∨ p1) ∨ True) → ((False ∨ True) ∧ p4)) ∧ ((p2 ∨ (((p1 ∨ p5) ∧ (False ∨ p1)) → p2)) ∧ (p1 ∧ p5))) ∨ (True ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54231161957020315412319925821 : ((((False ∧ ((True ∨ True) ∧ (p4 → True))) → p1) ∧ ((True → p3) → (((p5 ∨ p2) → False) ∨ ((p5 → (p2 ∨ (True ∨ p4))) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47532120594078192581545164737 : (((p4 ∨ (((p5 ∨ ((p1 → ((p4 ∧ False) → (p4 ∧ p1))) → p1)) → p5) ∧ (p1 ∧ (p4 → (p3 ∨ (True → p3)))))) ∨ (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111960243284832559118591750777 : (((((p2 → ((p2 ∨ False) ∧ (p5 → p3))) ∨ p3) → ((((p3 ∧ False) → p3) ∧ p5) ∧ ((p4 ∧ p4) → (p2 ∨ p1)))) ∨ p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64579181804036161199863366343 : ((p1 ∨ ((p1 → (True ∧ p5)) → ((p5 ∨ (((p3 ∧ ((p3 ∧ p3) ∧ p4)) ∨ (p4 ∨ True)) → (((False ∧ p2) ∨ p5) → p1))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790726445976400459465634775080 : (((p5 ∨ (True → (((False ∨ (((p5 ∧ ((p3 ∧ p4) → p3)) ∨ p1) ∧ (p1 ∧ p1))) → False) → (p5 ∧ (((p5 ∨ p5) → p3) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256472151951153792580663171754 : ((False ∨ p4) → ((p5 ∨ (((((p4 ∧ (False → (p4 ∧ ((p2 ∧ False) ∧ p3)))) ∧ p4) → p2) ∧ (p1 ∨ p1)) ∧ p2)) ∨ (p5 ∨ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892786304536110793945761120916 : ((((((False → (p3 ∨ (p5 ∨ ((((p5 → p3) → p1) → (p4 ∨ p3)) → True)))) → (p3 → p1)) → (False ∧ True)) ∧ ((p4 → False) ∧ p1)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((False → (p3 ∨ (p5 ∨ ((((p5 → p3) → p1) → (p4 ∨ p3)) → True)))) → (p3 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h6
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248758879906273202656778584519 : ((p3 ∨ p3) ∨ (((((p4 ∨ p5) ∨ ((p3 ∧ ((True ∧ (p5 ∨ (p3 ∨ True))) → False)) → (p5 ∨ True))) → p3) → p4) ∨ ((p5 ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_167902483301991994104877793692 : ((((p5 ∨ ((True ∨ p1) ∧ p2)) → (False ∨ p3)) ∧ (((p1 ∨ p5) ∨ p1) ∧ (p2 ∧ p4))) → (((p5 ∧ p5) ∨ p3) ∨ (p4 → (p5 ∧ p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p5 ∨ ((True ∨ p1) ∧ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h5.left
      let h16 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (p5 ∨ ((True ∨ p1) ∧ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351733047401208789523961553054 : (p4 → (((p2 ∨ (p3 ∨ (p2 ∨ p1))) ∨ (p1 ∧ (p3 ∨ ((p1 ∧ p2) → True)))) ∨ (True ∧ (p2 → ((True ∧ (p5 ∧ (p4 ∧ p5))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351812587357554577968044623539 : (p4 → (((((p3 → (p5 ∨ True)) ∨ ((p4 ∧ False) ∨ p2)) ∧ p4) → p3) ∨ (((True → True) ∨ True) ∧ ((p2 ∧ False) → ((p3 ∨ False) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157344314772432709617063418586 : (((p4 ∨ ((((((False ∧ p1) ∧ p5) → ((False ∨ (p3 → False)) ∨ p3)) ∨ True) ∨ p2) ∨ False)) → p5) ∨ (True ∧ ((p1 → (p1 ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_583258014643375994507650230760 : (((p5 → ((((p1 → p5) ∨ (p2 ∧ p3)) → (((False ∨ (p1 ∧ ((p2 → p5) ∨ False))) ∧ (p4 ∧ (p4 ∨ p5))) ∨ False)) ∨ (True ∧ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156250377087291920398033939815 : ((p3 ∨ (p3 ∨ (p3 ∨ (p2 ∨ ((p4 → p3) ∨ (((False ∧ p4) → p3) ∨ (False ∧ (p1 ∨ p3)))))))) ∧ ((((p1 → p1) → p1) → p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686108709792090368435303258894 : ((((((True ∧ (p2 → (True → (p5 ∨ ((p4 ∨ p5) ∨ p1))))) ∨ p1) ∨ (p4 ∧ (True ∨ True))) → (((False → False) → (p1 ∨ p1)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615367665772195445638039965972 : (((((((False ∧ p1) ∧ p1) ∧ ((p1 ∨ (True ∨ p4)) → (False → (p1 → (p2 → p3))))) ∨ (((p2 ∨ True) ∧ (False ∧ True)) ∧ p5)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_180980024552560356636723370258 : (((True ∧ True) ∨ ((True ∧ p2) ∨ ((p1 → (p2 → (p2 ∧ p1))) ∨ p1))) → (((p2 ∨ p1) ∨ ((p5 → ((p2 → False) ∧ p5)) → p2)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192939497969301568304098881805 : ((((p5 → (True ∨ True)) ∨ (p3 ∨ True)) ∨ (p3 ∨ p4)) → ((True → (True ∨ (p1 ∧ ((p2 ∨ p4) → (False ∧ p3))))) ∧ (p1 ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65510763304108788802847068785 : ((p3 ∨ (False ∨ (((((p1 → p4) → (p5 ∧ p5)) ∧ p4) ∧ (((p5 ∧ p3) → True) → p4)) → ((p1 → ((p2 ∨ False) → p3)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114362149301884911852369344391 : (((((p5 ∨ p1) → ((False → False) → ((p2 ∨ p2) → ((p4 ∨ True) → (True ∧ False))))) ∧ False) ∨ ((True ∨ (p2 ∨ p1)) ∨ True)) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678600327652700344757396629812 : (((((p2 ∧ p1) ∧ ((((p5 → ((p2 ∧ (p3 ∧ p4)) → p5)) → False) ∨ (p1 → (p3 ∨ True))) → p3)) ∨ (False → (True ∨ (True ∨ True)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158273768574657318836974337785 : (((p5 ∨ (p4 ∧ p1)) ∨ (True → ((((p5 ∧ p5) ∧ ((p5 ∧ p3) ∧ p5)) ∧ p1) ∨ (False ∨ False)))) ∨ ((False → ((p4 ∨ p2) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61447543200110604575909967124 : ((p1 ∧ ((p4 → ((False → (p5 ∨ (p4 ∧ p4))) ∨ ((False ∧ (((p4 ∨ (True ∨ p4)) ∧ p1) → False)) ∨ ((p1 ∨ False) ∨ True)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51505752979981993079850841301 : (((((True → p1) ∧ p3) → (p5 ∧ ((p4 ∧ ((p1 ∧ (p2 ∧ (False ∧ p1))) → False)) ∧ p2))) → (((p3 ∨ True) ∨ (p2 ∧ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350117030942919641134806796066 : (p4 → (((False ∨ (((p2 ∨ (((p4 ∨ True) ∧ (p4 → p3)) ∨ (p4 → (p3 → p2)))) → p4) ∨ p3)) → ((p4 ∨ (True ∨ p4)) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42407223030094179064148638241 : (((p5 ∧ ((((p1 ∧ p2) ∧ (((p3 → (p3 ∧ (False ∧ p4))) → (True → (p5 ∧ (False → (p5 ∨ True))))) ∧ p5)) ∧ p2) ∧ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211420977805110390941440312444 : (((p3 → p3) ∨ (p2 ∧ False)) ∧ (((((True → False) ∧ ((p5 ∧ p1) ∨ p3)) ∧ (False ∨ ((False ∧ p4) ∧ p4))) ∨ (True ∨ True)) ∨ (False ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_173567486926175311938189912160 : ((((p2 → False) ∧ ((p5 ∨ (p1 ∧ (p1 → p1))) → (False ∨ (p3 ∨ False)))) ∧ p1) → (((p3 ∧ p4) ∨ p3) ∨ (False ∨ (p3 ∨ (p5 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ (p1 ∧ (p1 → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215783672141318946790685712589 : ((p1 ∨ (p2 ∧ (True ∧ p5))) ∨ ((p3 → ((False ∨ ((True ∧ (p2 ∨ p2)) ∨ p3)) ∨ (((False ∨ (p1 ∨ p3)) ∧ False) ∨ True))) ∨ (p1 ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254271388323378743164385118585 : ((p2 ∧ p3) → (((p4 ∨ ((p3 ∨ (p5 ∧ False)) → p2)) → (((p5 ∨ (False ∧ (True ∨ p3))) ∧ (p5 ∨ p5)) ∧ (p2 → (p3 ∧ True)))) ∨ p3)) := by
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
theorem thm_5_vars_158076744388548977608652950273 : ((((p2 → (True ∧ False)) ∨ (p1 ∨ False)) → (((((p2 → False) → False) ∨ (p3 → True)) ∧ p5) → False)) ∨ ((p2 ∨ True) ∧ (p4 → (p1 → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245403420715603810713584243447 : ((p2 ∧ p4) ∨ (((((((((False ∨ ((False ∧ p3) ∧ True)) ∨ p3) ∧ p1) ∧ (True ∧ (p5 → True))) ∨ p3) ∨ p5) ∧ False) ∨ (True ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115513179593092698502810900091 : (((((p4 ∧ True) → p3) ∧ ((p2 ∨ False) ∨ True)) → (((p4 → (True ∨ (p3 ∨ (((p1 ∧ p1) ∧ p5) ∧ p5)))) → p1) ∨ p2)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116626234180135957593887572652 : (((p1 → True) ∧ (((p3 ∨ p1) → (p1 ∧ p2)) → ((((((p4 → (p5 → p4)) → p2) ∨ p5) → (p3 ∨ p3)) ∨ p4) ∧ p3))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778777281504846322600804839524 : (((p1 ∨ (p5 ∨ ((((p1 ∧ (((p3 ∧ p2) ∨ ((p4 ∨ (p1 ∨ (p5 → False))) → p5)) ∧ (p5 ∧ p4))) ∧ p4) → p2) ∧ (p4 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643258795264274306602491547135 : ((((p3 ∧ ((False ∨ (p2 → p3)) ∧ (p1 ∨ ((p3 → (p4 ∨ ((False ∨ ((p1 ∧ p5) → ((p5 ∨ False) ∨ p2))) ∨ True))) ∨ False)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313302463656871872055081526803 : (p3 ∨ ((False ∨ ((((p2 ∧ (True → (p3 ∨ ((False ∨ (p5 → p5)) ∧ ((p5 ∨ p4) ∨ p2))))) ∨ p1) ∨ (p3 → (p1 → p1))) ∧ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747808222002798205152323140581 : ((((False → p2) → (((p5 ∨ ((p3 ∧ p2) → (p4 ∨ (p2 ∨ True)))) → p2) → (p3 → ((p5 ∨ (p1 ∨ p5)) ∧ (False → (p2 → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119289718898199437640540228627 : ((p3 → ((p5 ∨ (((True ∨ p4) ∧ (((p2 ∧ p4) → p5) → ((p1 → ((p4 → (False → False)) → p4)) ∨ False))) ∧ p5)) ∨ True)) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66813766510187262451798426958 : ((True → (p5 ∨ ((((((True ∨ p1) ∧ (p1 ∧ p4)) ∧ p5) → p2) → ((p1 ∨ (p1 ∨ (p2 ∧ p4))) → p4)) ∨ (True ∧ (p4 → True))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346834269148494092838276072965 : (p3 → ((((p3 ∨ p5) ∨ (p4 ∨ p4)) ∨ ((p3 → ((p4 ∧ False) ∨ True)) ∨ (((True ∧ True) ∧ False) → False))) → (p1 ∨ (True ∨ (True → p1))))) := by
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
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792119662854043873100827129656 : (((True → ((p3 ∧ (p4 ∨ ((((p3 ∧ (p4 → p3)) ∨ p4) ∧ (True → ((p5 → True) ∧ p2))) ∧ (p2 ∧ True)))) ∨ ((True ∧ False) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244280757565367088890057636958 : ((False ∧ True) ∨ (((True ∧ p3) → p3) → (((p2 ∨ (True ∨ (p2 → p5))) ∧ p5) → ((p3 ∨ ((p5 ∧ p3) ∨ p2)) ∨ ((p1 ∨ p1) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179307454034719822715403501036 : ((False ∨ ((True → ((p4 → p4) ∧ p3)) → (p5 → ((p4 → p4) ∧ p2)))) ∨ ((((True ∧ p2) ∧ p4) → True) ∧ (False ∨ ((p1 ∨ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215326058487455399642602855572 : ((p1 ∧ (p5 ∧ (False ∨ p1))) ∨ (((p3 ∨ p1) ∧ (True → ((((False ∧ p4) → (True ∧ p3)) ∧ p2) ∧ p1))) → ((p2 → p5) ∨ (p1 ∧ True)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242795474874681023801225478948 : ((p3 → p3) ∧ ((True → (p1 ∧ (False ∨ ((p1 ∧ p2) ∧ (p2 ∧ ((p2 → (p4 ∧ (p3 ∨ p4))) ∨ (False ∧ (True ∨ (p4 ∨ p4))))))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257814617964045244362358860051 : ((p3 ∨ p5) → (((p2 ∨ ((p3 ∨ (p3 ∨ p5)) ∨ p1)) ∧ (False ∨ (p1 ∨ p2))) ∨ ((((p4 → p5) → p4) ∧ p4) → (p4 ∨ (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112250058222674238437739896112 : (((p4 ∨ ((((p5 ∨ (p4 → (((p2 ∨ ((p2 ∧ (p3 → p1)) ∧ p1)) ∨ (p4 → p4)) ∧ True))) ∧ p2) → False) ∧ p1)) ∨ False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324262271634858312016755128637 : (p5 ∨ (((p3 ∨ ((False ∧ False) ∨ p3)) ∨ (p5 → True)) ∨ (p4 → ((p3 ∨ ((False ∨ (p4 ∧ p3)) ∧ p4)) → ((False ∧ p3) ∨ (p2 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116710262668759928978818692347 : (((p1 ∧ p3) ∨ (p2 → ((p5 → (False → p2)) ∧ ((p3 ∧ (((p1 ∨ p3) ∨ p2) → ((False → p4) → p5))) → (p4 ∨ p5))))) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∨ p3) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350081373788428192998610894047 : (p4 → ((((p4 ∧ (p4 → p4)) ∧ (p4 ∧ ((p2 ∨ (False ∧ (False ∨ p4))) → (False ∧ (False ∧ (p4 ∧ (False ∧ True))))))) → (p4 ∧ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184443643059864913237888043866 : (((False ∧ ((p3 ∧ (p1 ∧ (p3 ∧ p4))) ∧ p4)) ∧ (True ∧ p4)) ∨ ((p2 ∨ (p5 → p5)) ∨ ((((p2 ∨ p2) ∨ p5) ∧ (p5 ∧ p4)) ∧ False))) := by
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
theorem thm_5_vars_757247813487563171183734129155 : (((p1 ∧ ((False → True) ∧ (((p5 → p4) → ((p2 ∨ p3) ∨ ((True ∨ p4) → (p3 → ((p4 ∨ ((p1 → p1) → False)) ∨ True))))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721692039287951067211469808242 : ((((False ∨ ((True ∧ p5) → p5)) → (p3 ∧ (p2 ∧ ((((True ∧ p4) ∨ p3) ∨ False) ∧ ((p4 → ((p3 ∨ True) ∧ p4)) ∧ (False ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682459471083552763937922301492 : ((((((p3 ∨ p2) ∧ (p5 ∧ ((True ∧ p5) ∨ ((p3 ∨ p2) ∨ False)))) ∨ ((True ∨ p4) → p2)) ∧ (True ∨ (p5 → (p1 ∨ (p5 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60212253631729276506292349760 : (((True → False) → ((False ∨ ((p1 ∨ p3) → ((True → ((p5 → ((p5 ∨ p3) ∨ p3)) → (True ∨ p2))) → False))) ∨ (p4 ∧ (False ∨ p1)))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615242191913961117772920644193 : (((((p2 ∨ (((p2 ∧ p4) → (p5 ∧ p3)) → ((p1 → (p4 ∧ False)) → (p4 ∧ p5)))) ∧ ((p5 → (False ∨ (p3 ∧ p1))) ∨ False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54162204290110425766310693250 : (((p5 → (((p4 → True) ∧ p4) ∨ ((p1 ∨ p5) ∧ p5))) → (True ∧ (True ∧ ((p4 ∨ p2) ∨ ((p2 → False) ∨ (False ∨ (True ∨ p1))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750088882789942407182737692258 : (((True ∧ ((p3 ∧ ((p5 → (((((p2 ∧ p4) → p1) → ((p5 → (p1 → (p1 ∧ p3))) → p1)) ∨ p4) → p4)) → (True ∧ True))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60718945639075704572648024479 : ((True ∧ ((((p1 ∨ True) ∨ (p1 → p2)) ∨ True) → (p5 → (((((p3 → ((p1 ∨ False) → False)) ∨ p4) → p3) ∧ p3) ∧ (p3 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797227915907198657330676458007 : (((p1 → ((((p1 → False) ∧ ((False ∧ ((((p4 ∧ ((False → True) → True)) ∧ (True → p4)) → False) ∨ p1)) ∧ (p1 ∧ p4))) ∧ True) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234923404632205573617949769979 : ((True ∧ True) ∧ (((True ∧ ((True ∨ p1) ∨ p1)) ∧ p2) ∨ ((True → (((True ∧ (p5 → p5)) → (True ∧ p1)) ∧ (False ∧ p4))) ∨ (p2 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234069936054496571732816972029 : ((True → (False ∧ False)) → (((((False ∨ (p5 ∨ p4)) ∨ (p5 → (p5 ∨ p1))) ∨ (False ∨ ((p3 ∧ (p2 ∧ p2)) → p2))) ∨ False) → (p5 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h10 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h11 := h1 h10
            -- We need to get the left conjuct of h11 based on <expert-advice>.
            let h12 := h11.left
            -- False on the left can always be used.
            apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h15 := h1 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h20
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h30 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h31 := h1 h30
            -- We need to get the left conjuct of h31 based on <expert-advice>.
            let h32 := h31.left
            -- False on the left can always be used.
            apply False.elim h32
          case inr h33 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h34 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h35 := h1 h34
            -- We need to get the left conjuct of h35 based on <expert-advice>.
            let h36 := h35.left
            -- False on the left can always be used.
            apply False.elim h36
      case inr h37 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h39 := h1 h38
        -- We need to get the left conjuct of h39 based on <expert-advice>.
        let h40 := h39.left
        -- False on the left can always be used.
        apply False.elim h40
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h44 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h45 := h1 h44
        -- We need to get the left conjuct of h45 based on <expert-advice>.
        let h46 := h45.left
        -- False on the left can always be used.
        apply False.elim h46
  case inr h47 =>
    -- False on the left can always be used.
    apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330854777077170587913349623483 : (True → (p3 → ((p1 ∧ (((p1 ∨ p3) ∨ p3) → (p3 → ((p3 → (False ∨ (p5 → (p1 ∨ p2)))) ∨ ((p5 ∧ p3) ∨ True))))) ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624017562392721696729712122521 : ((((p2 ∨ ((p2 → (p1 ∨ (p3 ∨ (((p1 ∨ (p2 ∧ p1)) ∨ ((p4 ∧ p1) ∨ p3)) ∧ (p5 → False))))) ∧ (p2 ∨ (True ∨ p2)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1502069729031918219703833478 : ((((False → True) ∧ ((p5 → ((((True ∧ (p5 ∧ (p5 ∧ p2))) → p2) → p3) ∧ p2)) ∨ p3)) → ((p3 ∧ p3) ∨ p1)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301700337719470364815876281378 : (False ∨ ((p1 ∨ True) ∧ (((p2 ∧ ((True → p2) ∧ ((p4 ∧ ((p1 ∨ p1) → p4)) → p3))) → (((p2 ∧ False) ∨ p1) → p4)) ∨ (p3 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320528262999824247218884383249 : (p4 ∨ (True ∧ ((((p3 ∨ p2) ∨ p3) → ((p2 ∨ p2) ∨ True)) ∨ (p5 → ((p4 → ((p5 ∨ (False ∨ False)) ∨ (p1 ∨ (p1 ∧ p1)))) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148831999304488109161198887582 : (((((p2 → p3) → p5) ∧ p1) ∧ (p4 ∧ (p1 → ((p3 ∨ (p4 ∧ (p2 → (p5 ∧ p2)))) → (p5 ∧ p2))))) ∨ (p4 → ((False ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63312251610012700998937729663 : ((p5 ∧ ((True → p3) ∧ ((((False ∨ ((p3 → p3) → (p5 → (p4 ∧ p4)))) ∨ p3) ∧ (p4 ∧ (p1 ∨ (p1 ∧ (True ∧ p4))))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140659741922129851221618399526 : ((((((p1 ∨ p4) ∨ p2) → p5) ∧ (p1 → ((p2 ∧ p5) → (p4 ∨ False)))) ∧ ((p2 ∨ (p5 ∧ (p1 ∨ p5))) ∧ p2)) → ((False ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



