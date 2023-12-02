variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72304573690103500121138030349 : (((p4 → (((p1 ∨ ((True ∨ ((False → ((p3 → p2) → ((True → (False ∨ p1)) ∨ (True ∧ True)))) → p3)) ∨ True)) ∧ p5) ∧ p3)) ∧ p4) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257986882147711370119790064919 : ((p4 ∨ p1) → ((p1 ∨ (((p2 ∧ ((((True ∨ (p5 ∧ True)) ∨ (False ∨ False)) ∧ p1) ∧ ((p5 → p3) ∨ p5))) ∧ p5) ∧ p4)) ∨ (False → p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111241964628247655249099775247 : ((((False → p4) ∧ (((p2 → (False ∨ True)) → ((p4 → p3) ∨ ((p2 ∧ p3) ∧ (False ∨ p1)))) → (p5 ∧ (True ∧ p2)))) ∧ False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225149238481820181456818487629 : (((p3 ∧ p2) ∧ p4) ∨ (((((p3 → (False → p3)) ∨ p5) → (p5 → (True → ((p5 → ((p2 ∧ p5) ∧ False)) ∨ p3)))) ∨ True) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20780057364435177056479546609 : ((((p1 ∨ (((((p1 ∨ p1) ∨ p1) ∨ True) ∨ False) ∧ p4)) ∧ p3) ∨ ((p4 ∧ p4) ∨ ((p1 ∧ True) → (False → (True ∧ (p3 ∧ p1)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190417594934258575142044433951 : (((p1 ∨ ((p5 ∨ (p4 ∧ (p1 ∨ p5))) ∨ p3)) ∨ p5) ∨ ((p4 ∧ ((p4 ∧ p2) → p1)) → (((p1 → False) ∧ p5) ∨ (p2 → (p2 → p1))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669155096327494820754090030231 : ((((((p5 ∨ (p2 ∨ (p1 ∨ p2))) ∧ (((((False ∨ p2) ∧ False) ∨ (False → (p1 ∧ p1))) ∧ p5) → False)) → p5) ∨ (p3 → (p2 → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112211560891431675192133950757 : (((False ∨ ((True → ((p4 ∨ (True → p5)) → (False ∧ p3))) → (((True ∧ ((p5 → (False → p4)) ∨ p1)) → p2) ∧ p3))) ∨ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111885027505743806569819860534 : (((((p3 ∧ ((((p2 ∧ (p2 → True)) ∧ (p4 ∧ False)) ∧ p1) ∧ p3)) ∨ p4) ∧ ((p5 ∧ p3) ∧ ((p2 → p4) ∨ p1))) ∨ True) ∨ (True → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166440319869303230826725657105 : ((p2 ∨ (((p1 ∨ p2) ∨ ((p3 ∧ p2) → (True → ((p3 ∧ (p1 ∧ p2)) → p3)))) ∧ p1)) ∨ (((p3 ∨ (p1 ∨ (False → True))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201748622481764459844416277205 : ((((False ∧ (False → False)) ∨ p2) ∨ True) ∧ ((p2 ∧ ((((p4 ∨ (p4 → True)) → (False ∨ (p2 ∨ True))) ∧ (p3 ∨ p3)) ∧ p4)) ∨ (False → True))) := by
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
theorem thm_5_vars_259514211071724301364394389849 : ((False → p5) → (((False → (p4 ∧ (p5 → (p3 → p2)))) → (False ∨ (p1 → (p4 → p1)))) → (((((p4 ∧ False) ∨ p1) ∨ False) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137723078719749691143273909484 : ((p1 ∨ ((p1 → p2) → (((p3 ∨ ((p5 ∨ (p3 ∧ (p3 ∧ True))) → p3)) → p5) ∨ (p1 → (True ∨ (True ∨ p3)))))) ∨ (False ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57812030559151524600835998259 : (((p2 ∧ (p4 → p2)) → (((p1 ∧ ((p1 ∧ (True ∨ p3)) → p4)) → (((False ∧ p4) ∨ p3) ∧ (p1 ∨ (False → False)))) ∨ (p5 ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_234845402880065282377987353593 : ((p5 → (p5 ∨ True)) → ((p5 ∨ p5) ∨ ((p3 ∨ (((((((p2 ∧ p5) ∧ p1) ∨ p5) → p3) ∨ (p4 → (p3 ∧ p1))) → p4) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115432993911875316581848610148 : ((((((False → p5) → p3) ∧ (p3 → p4)) → p1) ∨ (((p1 ∧ ((p3 ∨ (((p4 → p5) → p4) ∨ p1)) → p2)) ∨ p5) ∨ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_988421879879273449374201977701 : (((p3 ∧ (((((((p1 → ((p2 ∨ p1) ∨ p3)) ∧ p5) ∧ ((False ∧ p4) ∧ p2)) → False) → False) ∨ (p2 → (p1 → (p3 ∧ p1)))) → p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((((p1 → ((p2 ∨ p1) ∨ p3)) ∧ p5) ∧ ((False ∧ p4) ∧ p2)) → False) → False) ∨ (p2 → (p1 → (p3 ∧ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59386563362677679106294325226 : (((True → False) ∨ ((((p2 → p5) ∧ False) ∧ (False ∧ False)) ∨ ((p4 ∨ (p4 ∨ p2)) ∨ ((p1 → (True → (False ∧ (p3 ∨ p4)))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588457472768296870645508016261 : ((((((p2 ∧ False) ∧ ((((((p3 ∧ True) ∧ False) ∧ True) → ((p1 ∧ p2) ∧ True)) → (p1 → p5)) ∧ (p2 ∧ (False → True)))) ∨ p5) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319912259521399943206261108586 : (p4 ∨ (((True ∧ (p3 → True)) → False) → (p5 ∨ ((((((p1 ∧ (p5 → (p2 ∧ p1))) ∧ ((p1 ∨ p4) ∧ True)) ∨ p2) ∧ p1) ∨ True) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157798903774956027581735002734 : (((p2 ∨ ((p4 → (p2 ∨ (p1 ∨ False))) ∧ (p1 ∧ (p5 → p4)))) ∨ (p1 ∧ ((p5 ∧ p5) → True))) ∨ (True ∨ (True ∧ (p3 → (p5 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50664852722354635452451655801 : (((((False ∧ (True ∨ (p2 → False))) ∨ p5) ∧ (((p5 ∧ (p4 ∧ p1)) ∨ p1) ∨ ((p2 → p2) ∧ p1))) → (p1 → (p2 ∨ (p4 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737461837519263993236980685848 : ((((p4 → p5) ∧ ((p1 ∨ p4) ∧ (((((p2 → p1) → (p3 ∨ ((p4 ∨ False) ∧ p4))) ∨ (p3 ∨ p1)) → (True ∧ (p4 → False))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64790328722289841021935780189 : ((p2 ∨ ((((((((p4 ∨ p4) ∨ True) → p4) ∧ True) ∧ p5) → p5) → ((p5 → False) ∧ ((p4 ∨ (p2 ∨ (p4 ∨ p2))) → True))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323921224035882101667574388076 : (p5 ∨ ((((p2 ∧ (p2 ∨ (p1 ∧ p2))) ∧ (p2 → ((p3 → p4) → (True ∧ p1)))) ∨ False) → (p3 ∨ ((((p2 ∨ p1) ∧ p1) ∧ p5) ∨ True)))) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46049650556392742369506158875 : ((((p5 → ((((((((p3 ∧ (True ∨ True)) → (p5 ∧ p3)) ∨ p1) ∧ False) → p1) ∨ False) ∧ True) → (p1 ∨ p1))) ∧ p3) ∧ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184052269230001714118145355638 : (((((((False ∨ p4) ∧ True) ∨ p2) ∧ True) ∨ (p4 ∧ p3)) ∨ True) ∨ (((p2 ∧ ((True ∧ p3) ∧ True)) ∨ p1) ∧ ((p1 ∨ p3) ∨ (p5 ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257580950999329918585823047533 : ((p3 ∨ p1) → ((p3 ∨ (False → p3)) → ((p5 ∨ p1) ∨ (((((True ∨ p2) ∧ ((False → False) → (False → p1))) → p1) → p3) ∨ (False → p4))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741418898245766663670263790218 : ((((p5 ∨ p1) ∨ ((p3 → (((False ∨ p2) → ((((True ∨ p4) → p1) → p1) ∧ True)) ∧ (((False → p3) → False) → (False ∧ p1)))) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h14 := h8 h12
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219166149717715987170545894434 : ((False ∨ ((True ∨ True) ∨ p3)) → (p1 ∨ (p5 ∨ (((p5 → p4) → p3) ∨ (((((p1 ∧ True) ∧ (False ∧ True)) → (False → p1)) ∨ p4) ∨ p1))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134813052066274560736077151737 : (((True ∨ ((True ∧ ((p5 → True) → (((((p1 ∧ True) ∧ p4) → False) ∨ (p5 ∧ (p5 ∨ True))) ∨ p5))) → p3)) → p2) ∨ (True ∨ (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70557159756029821963979968936 : ((((((((p1 → ((p5 → p2) ∨ (True ∨ (p4 → p5)))) ∨ ((p3 → p3) → p1)) → p2) ∨ True) ∨ p2) → ((p2 ∨ p2) ∧ p4)) ∧ p3) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p1 → ((p5 → p2) ∨ (True ∨ (p4 → p5)))) ∨ ((p3 → p3) → p1)) → p2) ∨ True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48522482400917711950471566607 : (((((True ∨ (p5 ∧ True)) ∧ ((p4 ∧ ((False ∨ p2) ∨ p5)) ∨ ((p5 ∨ ((False ∨ p5) ∨ p4)) ∧ False))) ∨ True) ∧ ((p1 ∧ p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179143008122697617308384686941 : ((p1 ∧ (True → (((p5 ∨ p4) ∨ p4) ∨ ((p2 ∨ p3) ∧ (p5 ∧ p3))))) ∨ (((p3 ∧ ((True ∨ p4) ∨ ((p1 ∨ p1) ∨ p2))) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110703059825846035775441373593 : (((((p5 → ((p1 ∧ ((p4 ∧ ((p3 → p2) ∨ False)) ∨ (False ∧ p1))) ∨ ((False → p2) ∧ (p2 ∨ True)))) ∧ False) ∧ p3) ∧ True) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227749543819831639819966210309 : ((p1 ∧ (p3 ∨ False)) ∨ ((False ∨ ((p2 → p1) ∨ ((((p1 ∧ p3) → ((p2 ∧ (p3 ∧ (p2 → False))) ∧ p2)) → False) ∨ p1))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346779413558570547853649397321 : (p3 → ((((((p1 → ((False → False) ∧ (True → p3))) → True) → p4) → (p3 → False)) ∨ ((p2 ∧ p4) ∧ p5)) ∨ ((p3 → False) → (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64908609369263007141593795156 : ((p2 ∨ ((False ∧ (((p3 → p3) → (False ∧ p5)) ∧ (p3 ∨ ((True → ((False → p1) ∧ False)) ∧ p2)))) ∨ ((p2 → (p5 ∧ p1)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38215926972013934151735977271 : (((((p5 ∧ (p4 → (p2 ∨ p5))) ∨ (True ∧ ((p2 ∨ True) → (True ∨ ((p5 → p5) ∨ (p4 → p1)))))) → (True → (p2 ∨ p1))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118212442092584620176587857225 : ((p1 ∨ (((p5 ∨ (p2 ∨ (p3 ∧ p1))) ∨ (((p4 ∨ ((p4 → True) ∨ (False → False))) ∧ (p5 ∨ True)) ∧ (False → False))) ∧ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300063945335966882009343283145 : (False ∨ ((((((((p2 ∨ (p4 ∧ p1)) ∧ (p1 ∨ p1)) ∨ (p5 → p4)) ∨ (p5 ∨ False)) ∨ (False ∨ p1)) ∨ (p2 ∨ p2)) ∨ p3) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309312584673474833291409945427 : (p2 ∨ (((((p1 → (p5 ∧ (p2 → False))) → p4) → (((p4 ∧ (p2 ∨ ((p5 → (p5 ∨ p1)) → p3))) ∧ p3) ∨ p3)) ∨ True) ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716719721919757300593720208113 : (((((p1 → p5) → (p2 ∧ False)) ∧ ((((p3 ∧ (False → (False ∨ ((p4 → p2) ∨ ((p4 ∧ False) ∧ (p1 → p3)))))) ∧ p5) ∨ False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672336709632294062683502988897 : ((((((p3 ∨ ((False → ((p4 ∨ True) ∨ p5)) → (p3 → (p1 ∧ ((False ∨ p1) → p2))))) → (False ∧ p1)) → p2) → ((False ∨ p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158111697121512967353271090735 : ((((p3 ∨ p3) → (True → p1)) ∧ (p1 → (True ∧ ((p4 ∨ (p2 → p3)) ∧ ((p5 ∧ p1) → p3))))) ∨ (((p3 ∧ p5) ∨ p4) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171523671925630598212604362010 : (((((((p3 ∧ False) ∧ (p1 ∨ ((p3 ∨ True) → p3))) ∨ p2) ∧ p3) ∨ p4) ∨ p1) ∨ ((p5 → (p1 ∨ (p2 ∨ (p1 → (p3 ∨ True))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127733557703517170839673776160 : ((True → ((p4 ∨ ((p2 ∨ p4) ∧ ((False → True) ∨ ((((False ∧ False) → p1) ∧ p3) ∧ ((p5 → p3) ∧ (p5 ∨ p5)))))) ∧ False)) → (True ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43509493805963782009493013066 : ((((p2 ∨ (((p3 → (False → ((p2 ∨ ((p3 → ((p1 ∨ p4) ∨ p4)) → p4)) ∨ p4))) → True) ∨ ((p5 ∧ p5) ∨ p3))) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342878686504684898055603822357 : (p2 → ((p2 → ((p5 → (p2 ∧ p4)) → p5)) ∨ (p1 ∨ ((False ∧ ((p1 ∧ (p3 ∧ p5)) → (p1 → (p3 ∨ p2)))) → ((p5 → p2) ∨ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668884524488213089027820188557 : ((((((False ∨ p3) ∨ (((True ∨ p4) ∧ p2) ∧ ((p3 ∧ p5) ∧ ((True ∨ (p3 ∨ False)) ∨ (True ∨ False))))) ∨ p2) ∨ (False → (p2 → p5))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775236223222434239305447698920 : (((False ∨ ((p1 ∨ p2) → ((p3 ∧ ((((p3 ∨ p5) ∧ (True ∨ (p5 ∧ p2))) ∨ (p3 ∧ ((p3 ∧ p5) → (p4 → p2)))) ∨ p3)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57765304034744172013017970792 : ((((p5 → True) → p2) → ((((((p3 ∨ (((p5 ∨ (False → (p5 ∨ p1))) ∧ p3) → (p2 ∧ p5))) ∨ p5) ∧ p1) ∨ p3) ∧ p2) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50421378601981051951804530180 : (((p3 ∧ ((p2 → ((p4 ∨ ((((p2 ∨ False) ∨ p5) → p3) → (p3 → (p2 → False)))) ∧ p2)) → p1)) ∨ (p1 → (False → (p3 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232758841123578707186488385913 : ((p1 ∧ (p5 → True)) → ((((p1 → ((((p3 ∧ (p5 ∧ p1)) ∧ False) ∨ (p1 ∨ p4)) → ((p1 → (p2 ∨ p3)) ∧ p3))) ∨ True) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → ((((p3 ∧ (p5 ∧ p1)) ∧ False) ∨ (p1 ∨ p4)) → ((p1 → (p2 ∨ p3)) ∧ p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57096165007647693771042010630 : ((((p4 ∧ p5) ∧ p2) ∨ ((True ∧ (p4 ∨ (p2 ∨ (((False → False) ∨ p4) ∧ ((p5 ∧ ((False ∧ False) ∧ (p2 → True))) ∨ p3))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198413818820956559824011881577 : ((p4 ∧ ((True ∨ ((p4 ∧ p5) → False)) → False)) ∨ ((True ∨ (False → p4)) ∨ (p5 ∧ (((p3 ∨ ((p3 ∧ False) ∧ True)) → (True ∨ p1)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299212149817264765227610670503 : (False ∨ ((((p2 ∨ (((p4 ∨ p4) → ((p2 → p5) ∨ p5)) → ((p1 → (p3 ∧ p1)) ∧ ((p4 ∧ p5) → p5)))) ∨ p5) ∨ (p1 → p1)) ∨ p2)) := by
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
theorem thm_5_vars_107943486243266876994978962769 : (((p2 → False) ∨ (p4 ∨ ((p1 ∨ (((p3 ∨ ((p4 ∨ (p5 ∧ True)) ∧ p3)) ∨ True) ∧ p4)) → ((p1 ∨ p4) ∨ (p3 ∨ True))))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662326056286687185919424446695 : ((((((p5 ∧ (p4 ∨ (p2 → False))) ∧ (False → p4)) ∧ (p2 → (((False ∧ (p3 ∧ p5)) ∨ True) ∧ (p2 ∨ (p4 → p2))))) → (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153812594648588220863145152812 : ((p5 → (((((p1 → ((p3 → False) ∨ p3)) ∨ (p4 ∧ False)) ∧ (p3 → False)) ∧ (p3 ∨ p2)) ∨ (p2 → p1))) → (((p3 ∨ False) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160686282925207309938427121739 : ((((p3 ∧ True) ∧ (((False → p4) ∨ p1) → p5)) ∧ (p4 ∨ (p4 ∧ (((True ∨ p1) ∧ p1) ∨ True)))) → ((False ∧ ((True → p1) → False)) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((False → p4) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : ((False → p4) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h20 := h5 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h22 : ((False → p4) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h22
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h25 : ((False → p4) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h26
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h27 := h5 h25
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57155085865060081922450345542 : ((((True ∧ p5) ∨ p4) ∨ ((((((False ∧ p2) ∨ ((p2 → False) ∧ p5)) ∧ p4) ∨ (True → (p5 → False))) ∨ (p4 ∧ (p1 ∧ p5))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168063553624644440729909502370 : (((((True ∨ p1) ∧ p3) → p5) ∧ ((((True → p2) → p4) → p3) ∧ (p5 → (p1 ∨ False)))) → (((p1 → True) ∧ (p5 ∧ p2)) → (p1 ∨ p5))) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185051099352672023996855647180 : (((p5 → p4) ∧ (((p1 ∨ ((p3 ∨ True) ∨ p4)) → False) → False)) ∨ (((p5 ∨ (p1 ∨ p1)) ∧ ((p4 ∨ p3) ∧ p3)) ∨ (True ∨ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302763763782014150604590508452 : (False ∨ (p4 ∨ ((((True → (((p5 ∨ p3) → p1) → p3)) ∨ p1) ∨ True) → ((p1 → (p3 → ((p1 → p3) → p1))) → ((p5 ∨ p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38387246938176502636531577379 : ((((((True ∨ (True → (p1 → p5))) ∧ (p3 ∧ (False → (p5 ∨ True)))) ∨ (p4 → p5)) → (p3 ∨ (p4 → ((p4 ∧ p5) → p3)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4594682374460917196933488963 : (p4 → ((p4 ∧ ((p2 ∧ True) ∨ ((True ∧ p4) ∧ (p4 ∧ p4)))) → ((p3 ∧ p1) ∨ ((((p5 ∨ (p1 ∨ p4)) ∨ p4) ∨ p5) ∧ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51239641424827350068789014268 : (((((p5 ∨ p4) ∧ p3) ∨ (p5 → ((False ∨ (p5 ∧ (p5 → (p5 ∧ (p4 ∨ p4))))) ∧ False))) ∨ (((p3 ∧ (False ∧ p3)) ∧ p2) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130440118394763874908174263328 : (((((True ∧ (p4 ∨ (((p1 → p2) ∧ p4) ∨ False))) ∧ True) → (p2 ∧ ((p5 → p3) ∧ p4))) ∨ (p2 ∨ (p5 ∨ True))) ∧ ((p3 ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180967929417277832674296898246 : (((p2 → True) ∧ ((((True ∨ (p2 ∧ p2)) ∧ p4) ∨ True) → (True → p3))) → ((((p5 → (((p3 ∧ p2) ∨ p3) → False)) ∨ p3) ∨ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∨ (p2 ∧ p2)) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53389609327008324208886096826 : ((((p5 ∨ ((p4 ∨ (True ∧ p4)) → (p4 ∧ (p5 → p2)))) → p3) → ((p5 ∧ (p2 ∨ (((False ∨ True) ∧ False) ∨ True))) ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60451389823345600356349522499 : (((p5 → False) → (True → ((p4 ∧ ((p5 → p1) → (False ∧ p2))) → ((p4 → (p3 → p5)) ∧ (p1 ∧ ((False ∨ (False ∨ p3)) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38683246831432412391728721637 : ((((True ∨ (True → (p3 ∨ (p5 ∨ p2)))) ∧ ((p5 ∧ ((p5 → p2) → p1)) → (True ∧ ((False ∧ p1) ∨ ((True → True) → False))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47729367353576114739861093031 : (((((p1 → (p5 ∧ (False ∨ ((p5 ∨ (p3 ∧ ((p5 ∧ False) ∧ (p2 ∧ p5)))) ∧ (p4 ∨ p1))))) ∨ (p3 ∨ False)) ∨ True) → (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218087438204694831482611848441 : (((True → p2) ∧ (p4 ∧ True)) → ((False ∧ ((((True ∧ p4) ∨ (False ∧ p2)) → (p2 → (p5 ∧ p5))) → p1)) ∨ ((True ∨ True) → (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356907745596265443573811026124 : (p5 → (((p4 ∨ p4) → (p4 ∧ p3)) → ((((False ∧ (((p4 → (((p2 ∨ True) ∨ p1) ∧ (False ∨ True))) → p4) ∧ p4)) ∨ True) ∨ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299213199285276268948050482177 : (False ∨ ((((p3 ∨ (((True ∧ ((True ∨ ((p3 ∨ False) ∧ (p4 ∧ p3))) → (p1 → p5))) → p3) ∨ (p2 ∧ p2))) → False) ∨ (p1 → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163024341098641013864533022687 : ((((((True ∨ (p3 ∧ p1)) → p5) ∧ p1) ∧ ((p3 ∨ p1) ∨ False)) ∨ ((p2 ∧ p2) → True)) ∧ ((p2 ∨ p2) → ((p1 → (p5 ∧ False)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
theorem thm_5_vars_204631271042093298299847821027 : (((False ∧ ((p3 ∧ False) ∧ p2)) ∨ p5) ∨ ((p1 ∨ p3) ∨ (((p1 → (p4 ∨ True)) ∨ (((True ∨ p2) → False) ∨ (True → (p5 ∧ False)))) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161408871373342956261005697042 : ((p1 ∧ (p4 ∨ (p4 ∨ ((p5 ∧ ((p5 ∨ (p3 ∨ p2)) ∧ False)) ∨ (((p1 → p1) ∧ False) ∧ True))))) → (((p5 → (False ∧ p3)) ∧ p3) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- False on the left can always be used.
            apply False.elim h12
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h12
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168607112736318020243219785953 : ((p3 ∧ ((p5 ∧ ((False ∧ p3) ∨ ((p4 ∨ False) → ((p1 → (True ∧ p2)) → p4)))) → p5)) → (((True → p1) ∧ False) ∨ (False → (p5 → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52418769907330677180258950609 : ((((p4 ∧ p4) ∧ (p1 ∨ ((p1 → p3) ∧ (p2 ∨ ((True ∨ p3) ∨ p1))))) ∧ ((True ∧ p2) ∨ (((p1 → p3) → (p3 → False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41121560890765150233717130838 : ((((p3 → ((((p1 → (False → (p4 → (p5 ∨ (p5 ∨ ((p4 → p5) ∨ p4)))))) ∨ p5) → p4) ∧ False)) ∧ (p1 → (True ∧ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189641832778433625646850871063 : ((p1 ∨ (True ∨ (p4 ∨ ((True → (True → False)) ∧ p3)))) ∧ (p5 ∨ (p1 ∨ ((((p1 → p5) ∧ (p4 ∧ True)) ∨ ((True → p2) → True)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41658140615382161452553829615 : ((((p4 ∧ (True → (False ∧ (True ∧ p4)))) ∧ ((p2 ∧ (((p3 ∨ (p4 → p3)) → p2) → ((p2 ∧ p4) ∧ (p5 → p4)))) ∨ p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194095294749590199830382445844 : ((True → (p5 → (p3 ∧ (((False ∧ p5) ∨ p1) ∧ p1)))) → (p4 → ((p3 ∧ ((p5 ∧ ((p3 → p2) → p4)) → (p1 ∨ (p1 ∧ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702724378941061213619017225370 : (((((False ∧ ((True → False) ∧ (p3 ∨ p1))) ∨ (p3 → p5)) ∨ ((p3 ∨ ((p2 ∧ (p5 ∨ (p3 ∧ (p2 ∨ p3)))) → p2)) ∨ (False ∨ False))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204233896263272208868597391884 : ((((False ∧ p2) ∧ (p3 ∧ p5)) ∧ p2) ∨ (True ∨ ((p4 ∨ p1) ∨ (((False ∧ p3) ∨ (True ∨ ((p5 → True) ∨ p5))) ∧ (True → (p3 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234488678192285769738984884183 : ((p2 → (p4 ∨ p3)) → (((p3 ∨ p3) ∧ p5) ∨ ((p1 ∨ (p4 ∨ p1)) ∨ (((p4 ∧ False) ∨ ((False → (p3 → p1)) ∨ (p2 ∧ False))) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39864462715017587487449746823 : (((p2 → ((((p4 ∨ p1) ∨ (p1 ∨ ((p3 ∧ ((((False → True) ∧ p2) → (p5 ∨ p1)) ∨ p3)) → (p3 → p2)))) ∧ False) ∧ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141281058486207216571216843137 : ((((p1 ∨ (p2 ∧ False)) → p4) ∧ ((((False ∧ (p2 ∨ (True ∧ p3))) → p1) ∨ p2) ∧ (((p1 ∧ p2) ∨ True) → False))) → ((p1 → False) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h21 : ((p1 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41257581126077345890588699433 : (((((p5 ∨ (p2 → (p1 ∧ (p1 → False)))) ∧ ((False → (p3 → ((False ∨ p5) ∧ p2))) ∧ p3)) ∨ ((p2 → p5) ∨ (False ∨ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255618090107608140906548514757 : ((p5 ∧ p4) → ((((p5 → p5) ∨ p3) → (((False ∨ ((True ∧ True) ∧ (p4 ∧ ((True → False) ∨ False)))) ∨ True) ∨ (p3 ∨ p5))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596540694624631249741013631691 : ((((((True ∨ p5) ∧ (((p4 ∧ p5) ∧ p5) ∧ True)) → ((p1 → ((p3 ∧ ((p2 ∧ True) ∨ False)) ∧ (True ∨ p5))) ∨ (p5 ∧ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144520922101620210501324419862 : ((((True → ((True ∨ (((p2 → False) → p3) ∨ ((p1 → p4) → p3))) → (False ∧ p4))) ∨ True) ∨ (False ∧ p5)) ∧ (False → (True → (False ∨ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327171451738404569884753453624 : (True → ((False ∨ (((p1 → (p2 ∨ ((((p2 ∨ (p3 ∨ False)) → ((False ∨ p4) → (p1 ∨ p2))) ∨ p1) → (p2 ∨ p3)))) ∧ True) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110916547644750026669355682757 : ((((p2 ∨ ((p5 ∨ p1) ∧ (p5 ∧ (p5 ∨ (((p3 ∨ p5) ∧ False) → (p4 ∨ (p2 → ((p1 → p3) ∨ False)))))))) → p3) ∧ p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173505027577573565804464831112 : (((((((p5 → p5) ∧ True) ∧ (True ∨ (p2 ∧ p4))) ∨ p3) ∨ (p1 ∨ p1)) ∧ p5) → ((p4 ∧ (((False → True) → p4) → (p4 ∧ p3))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h14 : ((False → True) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h14
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h21 : ((False → True) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h21
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h28 : ((False → True) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h30 := h4 h28
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h32 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h33 : ((False → True) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h34
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h35 := h4 h33
      -- We need to get the right conjuct of h35 based on <expert-advice>.
      let h36 := h35.right
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306440859252687348228724912117 : (p1 ∨ ((False ∨ p5) ∨ (((p1 ∧ (p1 → False)) ∧ (p4 → p2)) → ((p5 ∧ ((((False ∧ False) ∧ (p4 → p3)) → p3) ∨ True)) ∧ (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65341638762989129642530127510 : ((p3 ∨ (((p1 ∨ p5) ∧ ((p5 ∨ ((p4 ∧ False) ∧ True)) → (p2 ∧ (p1 ∨ (True ∨ False))))) ∧ (((p4 ∨ p1) ∧ p1) ∨ (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



