variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778692721352023209081144241790 : (((p1 ∨ (p3 ∨ (((((False ∧ (((False ∨ True) ∧ p1) ∧ p1)) ∨ False) ∨ (p4 ∨ True)) → (p4 ∧ (p2 → ((p5 ∧ p3) ∨ p3)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670409320387251241807793217288 : ((((((p5 ∨ p3) → p2) → (((p4 ∧ (p3 ∨ (((True ∧ (p2 → True)) ∧ p2) ∧ (True ∨ p2)))) ∨ p5) ∨ p5)) ∨ ((p3 ∨ False) → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_306168668910824182649594073112 : (p1 ∨ (((p4 ∨ True) → p4) ∨ (p3 ∨ ((p2 ∨ p4) ∨ (((p4 ∨ (p5 ∧ p2)) ∧ (p5 ∧ False)) → (p5 → (((p5 ∨ p4) ∧ True) → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55186256450711775456897440043 : (((((p1 ∧ p2) → (p2 → True)) → p1) ∨ (((((p5 ∨ (False → p1)) ∧ (True ∧ True)) ∧ p2) → p2) ∨ ((False ∨ p5) → (True → p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208239189112783117454479671269 : (((p1 ∧ p3) ∧ (p3 → (p2 ∨ p5))) → ((p5 ∧ p5) ∨ ((p3 ∧ (p4 ∧ p3)) ∨ ((p2 ∧ (((p2 → (False → False)) ∨ True) → p2)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600389230134685536098837591518 : ((((True ∧ ((((p2 ∧ (p4 ∨ ((((False ∧ (True → p5)) ∧ (False ∨ p4)) ∨ (p3 ∨ p5)) ∧ p2))) ∨ p4) → (p4 ∨ p1)) → p2)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305690459343615376099021477536 : (p1 ∨ ((p4 ∨ ((p1 ∧ ((p4 → True) ∨ (False ∨ p3))) ∨ p1)) ∨ (p3 → (p5 ∨ (((((p3 ∧ (True → p4)) → p2) ∨ False) ∧ p4) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61270752245856144576819415139 : ((False ∧ (p2 ∨ (((p3 → (p5 ∧ (((p2 → p1) ∨ (True ∨ ((p2 ∨ p2) ∧ p2))) ∧ p5))) ∧ True) → ((p2 ∨ (True → p4)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157326619174782467476124491842 : (((True ∨ ((((p4 → p1) → (((p3 ∨ (p2 ∨ p1)) ∨ p5) ∨ (p5 → p1))) ∧ p3) → p1)) → p2) ∨ ((p2 → p1) → (True → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158800264765895888965603597195 : ((p5 ∧ (((p2 ∨ p4) ∨ p1) ∨ ((p2 → ((p2 ∧ (((False ∨ p1) ∨ p3) ∧ p3)) ∧ False)) ∨ p3))) ∨ ((((p3 → True) ∨ p3) ∧ False) → False)) := by
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
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246089261050074050327262559229 : ((p4 ∧ p1) ∨ ((((p4 → (((p2 → p3) ∧ ((False ∧ p3) ∨ p5)) ∨ p4)) → p2) → (p3 ∧ (p4 → False))) ∨ ((p3 → p3) ∨ (False → p3)))) := by
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
theorem thm_5_vars_135148106025482405176876168964 : (((True → (((False ∧ p2) ∧ ((p2 ∧ p2) ∧ ((p3 ∧ (p4 → p3)) → (p2 ∧ (True ∨ True))))) ∨ p3)) ∨ (False → p3)) ∨ ((p2 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1474331249458634078909255131 : (((p2 ∧ ((((p3 → (False → True)) ∧ (((p5 ∧ p4) ∨ (True ∨ p3)) → False)) ∨ ((p2 → True) ∧ p4)) ∧ p4)) ∨ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238322305490028604611089785474 : ((False ∨ True) ∧ ((True → (((p4 ∨ ((p2 ∨ p4) ∨ p1)) ∧ p4) ∧ p5)) → (((p2 → (p5 ∨ (((p5 ∨ p1) ∨ p1) ∧ p2))) → p1) → p4))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300415906825066241748359243324 : (False ∨ ((p3 → (False ∨ ((((p5 ∨ (p1 ∧ True)) → p3) → (((p2 ∨ ((p4 ∨ p1) → False)) → p3) ∧ p2)) ∨ p5))) ∨ (False ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_174891097150324118365275318586 : (((p1 ∧ p2) → (((p5 ∨ (p5 ∨ False)) → (p1 → ((p1 ∨ True) ∧ p5))) ∨ p2)) → (((p2 ∨ p4) ∨ ((p4 ∨ True) → (True ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116153272919403816311145937409 : (((p2 ∨ (False ∧ p1)) ∧ (((p5 → (True ∨ p5)) → (False ∧ ((((p2 → True) → p4) ∨ p3) → False))) ∨ ((p5 ∧ True) → False))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310016701568575357379664161625 : (p2 ∨ (((((False ∨ p2) ∨ p1) → (True ∧ (p3 → (p1 ∨ (False ∧ (p3 ∨ p1)))))) ∧ p1) ∨ (p4 → (True ∨ (p5 → ((False ∨ p2) ∨ p5)))))) := by
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
theorem thm_5_vars_299353290149069861002304861428 : (False ∨ (((False ∨ (p5 → p3)) → (((p5 → ((p4 ∨ p4) ∧ p4)) ∨ ((p2 ∧ ((p2 ∨ p3) → p3)) ∨ (False → (p1 ∧ p1)))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223831116048071892550634473568 : ((p3 ∨ (True ∨ p1)) ∧ (((((p3 ∧ p5) ∨ (p5 ∨ True)) → p4) ∧ (False → ((p2 → p2) ∨ (p3 ∧ p2)))) → (p4 ∨ (p2 ∧ (p1 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ p5) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809042099166564005856031480009 : (((p5 → ((False ∧ ((p1 → (p2 → (((p3 ∨ (p3 ∨ (p3 → p1))) ∧ (False ∧ True)) ∨ p5))) ∧ (p5 ∧ ((p2 → p2) ∧ p5)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315164888890913916052635407054 : (p3 ∨ (((p5 → p1) ∨ (True ∨ (p5 → True))) → (((p5 → True) → p3) → (((p3 ∨ p4) ∨ (((p5 ∧ (p4 ∧ p1)) ∧ p5) → p5)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186019542055068882122152905297 : (((p4 → ((p3 ∧ (p2 ∨ ((True → False) → p3))) ∧ False)) ∧ p4) → ((p4 ∧ ((True → (p4 ∧ p1)) ∧ (((p2 ∨ p3) ∨ p4) ∧ p1))) → p1)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174166917076569325272645149197 : ((((p3 → p3) ∧ (((p4 → ((False ∧ p3) ∨ p5)) → False) ∧ p4)) ∨ (p1 ∧ p3)) → ((((p1 → False) ∨ p3) ∨ ((p3 → p1) → p3)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599556903615826970724632352253 : (((((p3 ∨ p5) ∨ (False ∨ ((((((p3 ∧ ((p1 ∨ p3) ∨ (True ∧ p5))) ∨ False) → (p2 ∨ p3)) ∧ (p3 → p2)) → p2) → p2))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70063808606403645108537472932 : (((((((True ∧ p2) ∧ p3) ∧ (p2 ∨ (p2 ∧ (p5 ∨ ((True ∨ ((False ∨ p2) ∧ True)) ∧ p1))))) ∨ ((p5 ∧ p4) → p5)) → False) ∧ True) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∧ p2) ∧ p3) ∧ (p2 ∨ (p2 ∧ (p5 ∨ ((True ∨ ((False ∨ p2) ∧ True)) ∧ p1))))) ∨ ((p5 ∧ p4) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193963497470932628549606038118 : ((p2 ∨ (p1 → (False → ((p1 ∨ (p1 ∨ p4)) ∨ p4)))) → ((((True ∨ False) → False) ∧ (p2 ∧ (p3 → p4))) → (((p1 ∧ True) ∨ True) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h20 := h14 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h22 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h23 := h14 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385942449186156316806633338841 : (((((((p4 ∨ (p1 ∨ p3)) ∧ (((p1 ∨ p4) ∧ (p1 ∨ (True → (((p2 ∧ p3) ∧ p1) ∨ p4)))) ∨ True)) ∧ True) ∨ (p4 → p4)) ∨ p4) ∧ True) ∧ True) := by
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
theorem thm_5_vars_619943826721643156535748755173 : (((((False → p4) ∧ (((((p4 ∨ True) ∨ p2) ∧ p5) ∧ ((p1 ∨ p2) ∧ (((p1 → False) ∨ (p4 ∨ (p2 ∧ p3))) ∨ p2))) ∨ True)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61464057171421412434298509641 : ((p1 ∧ (((p5 ∧ ((((p5 → p2) ∧ p1) ∨ ((p1 ∧ p1) ∧ p3)) ∨ (p4 → p4))) ∨ ((False ∨ (p2 ∧ p5)) ∧ p2)) ∨ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321646213727348209555957515141 : (p4 ∨ (p3 → (p1 → ((((p5 ∨ (p4 ∧ True)) ∧ True) → p2) → (p3 ∧ (((p3 → (((p1 ∧ p4) → False) → p5)) ∨ True) ∨ (True → True))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303753005589554108628784502061 : (p1 ∨ ((((((False ∨ (p1 ∧ p1)) ∨ p3) → ((p4 ∨ False) → (((((p4 ∨ p1) → p3) ∧ (False ∧ p3)) ∧ p3) ∧ False))) → p1) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732137189993175096370989176995 : ((((True ∧ p3) ∧ (((((((p5 ∨ p1) ∨ ((p2 → p3) → p5)) → p3) → p5) ∧ (p5 → p2)) ∧ (p5 ∨ p2)) ∨ (p3 ∧ (p1 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118326873704829600223828970288 : ((p2 ∨ (((((p3 → p3) ∨ p4) ∨ ((False ∧ (False ∨ p5)) → ((p1 ∨ p5) ∨ (((p5 → p5) ∧ p1) → True)))) → False) ∧ p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248026883033958076056287994078 : ((p1 ∨ p5) ∨ ((((p2 → p5) → p1) → (((((True ∧ p2) ∧ p3) ∨ p1) ∨ False) → (p4 → (((p2 ∨ False) ∨ False) → p5)))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68076083997867482025738166330 : ((p2 → (p3 ∨ ((False ∧ ((True → (((False → ((True ∧ True) ∨ (((False → p3) ∧ p5) ∨ p3))) ∨ p4) ∧ True)) → (p4 ∧ p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37446208058354673503913927786 : (((((p2 ∧ (((p4 → ((p4 ∧ (p3 ∧ False)) → p1)) → p5) ∨ (True ∧ p4))) ∨ (p4 ∧ (True ∨ (p4 ∧ (p1 → False))))) ∨ True) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340759020804557947364550938874 : (p2 → (((p4 ∧ ((((False → (False ∧ ((False → p5) ∨ p5))) ∨ (p3 ∧ p5)) → ((p1 ∧ (p2 ∨ False)) ∨ p4)) ∧ (p4 ∨ p2))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150529109515637895905735116240 : ((((((p4 → ((p2 ∨ True) ∨ p4)) ∧ True) → (p5 ∧ p5)) → (((p4 ∨ (p4 ∨ p5)) ∧ p2) ∧ p4)) ∧ p5) → ((p5 → False) → (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42888583750163278412312069476 : (((p3 → ((((True → p1) → ((True → (p5 ∨ True)) ∨ False)) ∨ ((True → (((p2 ∨ p1) → (False ∨ p1)) → p5)) ∧ p4)) → p4)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463260424938257884041853683263 : (((((p5 → (p3 ∧ True)) → ((p4 ∨ (p2 ∨ p4)) ∨ ((p4 ∨ (p5 ∨ True)) ∨ p4))) ∨ ((p3 ∧ ((True → True) ∨ (p2 ∨ p5))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125086972702338320364726810143 : (((p4 ∨ (p1 ∧ p4)) ∧ ((((p5 ∨ p1) ∨ p1) ∧ (((p5 ∧ ((p5 ∨ (p1 ∨ p3)) → True)) ∧ True) → (p1 → p3))) ∨ p4)) → (p3 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244265329180143422174816518414 : ((False ∧ True) ∨ ((True ∧ (((p3 → (((p4 ∧ (p4 → p3)) ∨ True) ∧ ((p2 ∨ p5) ∧ p2))) ∨ (p4 ∨ True)) ∨ False)) ∨ (p3 ∧ (p5 ∧ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238133447516634335035812193447 : ((True ∨ p3) ∧ ((((p2 ∧ p5) ∧ ((((p5 ∧ (p3 → p4)) ∨ False) → (False ∧ (True ∧ False))) → False)) ∧ False) ∨ (True ∨ (p3 → (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41695714761583413391999337499 : (((((p2 → (p3 → (p4 ∧ True))) ∨ p4) → (p4 → (((((True → p4) ∨ (p1 ∨ p3)) ∨ (p4 ∨ p4)) ∧ p5) ∨ (p4 ∨ p4)))) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57191060077553035455029308440 : ((((p2 ∨ p4) ∨ False) ∨ (p2 → (((p1 → (((p3 ∨ (False → (p3 ∨ p2))) ∨ (True ∧ ((p3 ∨ p4) ∧ True))) ∧ p3)) ∨ p4) ∨ p2))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785993336593516775749280007074 : (((p4 ∨ ((False ∧ (True ∧ ((p3 ∧ (p2 → (p3 → (True → (((p3 ∨ p1) → (p2 ∧ (p3 → p2))) ∧ p2))))) → p1))) ∨ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52026803369003652504999304007 : (((p1 ∨ (p5 ∨ (p2 ∨ ((p4 ∧ (p5 → (p5 ∨ p4))) → (p2 ∨ (p4 → p5)))))) ∨ (p4 → (((p5 ∧ p1) ∨ (p3 ∨ True)) ∨ True))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233229187714208259083990028280 : ((p5 ∧ (p4 → p3)) → (True ∧ (((((p5 → (p2 ∧ (p1 → True))) ∧ False) ∧ p3) ∨ ((((p3 → (p2 → p3)) ∧ p4) ∧ p1) → p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168938690960762608111205753309 : ((True → ((p2 ∧ (p5 → (p2 ∨ (True → p3)))) ∧ (p3 ∧ (False → (p5 ∨ (p4 ∨ False)))))) → (((p2 → p1) → (p3 ∨ (p1 ∨ p2))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2191846131619302142196461753 : ((((p4 ∨ p4) ∨ (p5 ∧ p1)) ∨ (((False → (p1 ∧ (False ∧ False))) → p4) ∨ True)) ∨ (p1 → (p2 → ((False ∨ (p5 → p3)) ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136346717994859087074648897465 : (((p4 ∨ ((p2 ∧ p4) ∧ p5)) ∧ ((p2 → (((p1 ∧ ((False → p5) ∧ p4)) ∨ (p3 → (p5 ∨ p2))) ∨ p4)) ∨ p4)) ∨ ((False ∧ p5) → p3)) := by
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
theorem thm_5_vars_22180128057511111386734712327 : ((((p3 → p2) → (p1 ∨ (True ∧ (p3 ∨ p1)))) ∨ (True ∧ ((p5 ∧ ((p4 ∨ ((p3 ∧ (False → p1)) → p1)) ∨ True)) → (p3 ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61141693350374303010745275154 : ((False ∧ (((p2 ∨ p2) ∧ ((p1 ∧ False) ∧ p5)) ∨ (p4 ∨ (((p1 ∧ ((((True ∧ p2) ∧ p2) ∧ p3) ∧ (False → p5))) ∨ p4) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186239169438635567085342370648 : (((((((p1 → p4) ∧ p1) ∨ (True ∧ False)) ∨ True) ∧ True) → p5) → ((True → (((p3 → (False ∨ p1)) ∧ p4) ∨ ((p3 → p3) ∨ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54509271576877545857125089947 : (((((p2 → p4) ∧ p2) → (p2 → (False ∧ p4))) ∨ ((p1 → (p4 ∨ (False ∧ ((p2 ∨ (p5 → (p5 ∨ False))) → p5)))) ∨ (p1 ∨ True))) ∨ False) := by
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
theorem thm_5_vars_147256067744315312585328800358 : ((((True → (((p3 ∧ (p1 ∨ (True ∧ (p1 → False)))) ∨ (p4 ∨ (p4 ∧ (p4 ∧ False)))) ∧ p2)) ∧ p5) ∨ True) ∨ (((True ∧ True) → p4) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135566125276377815508244315967 : (((p1 → (((p4 ∧ p3) → p1) → ((p2 → ((False → p5) ∧ False)) → (p3 ∨ p2)))) ∧ (((p2 ∨ p4) ∧ False) ∨ p1)) ∨ (p4 → (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256518890216773290685531618644 : ((False ∨ p5) → (((False ∨ False) ∧ ((False → ((((False → (p4 ∨ p2)) ∧ p2) ∨ (p5 → p2)) → (p1 → (p1 ∧ p1)))) → (p1 → p3))) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340340899123915041432245335765 : (p2 → (((p3 → (((p5 ∧ True) ∧ p4) ∨ (p2 ∧ (((p2 ∨ p3) ∨ (((False ∨ (False → p1)) ∨ p1) ∨ (p3 → False))) ∧ p4)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117705046795990079037005099820 : ((p3 ∧ (p1 ∧ (p3 ∧ (((((p5 ∨ True) → False) ∧ True) ∨ ((p5 → p2) ∧ (p3 ∨ ((p3 → True) → (p1 ∧ False))))) → p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351003783777362480007568058790 : (p4 → ((p2 ∨ (((True ∨ ((p5 ∧ p3) ∧ p2)) ∧ ((((False ∧ (False → False)) ∨ (p5 ∧ (p5 → p5))) ∨ p2) ∧ p5)) ∧ p2)) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635598867725258471183241584688 : ((((((p1 ∧ (((p5 ∧ False) ∨ p1) ∨ True)) ∨ ((((p1 ∨ p4) ∨ p1) ∧ (p4 → p4)) ∧ p2)) ∨ (False ∧ ((p1 → p5) → p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42598951490585883496517887420 : (((p2 ∨ (p3 ∨ (False ∧ ((((False ∨ (False ∧ p2)) → p1) → p5) ∧ (p4 → (((False ∧ (p3 ∨ p2)) ∨ (p1 ∨ p1)) ∧ p3)))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258919292048781489242439054978 : ((True → p2) → ((p5 ∧ p5) ∨ ((((p3 → (p4 ∧ (((((True ∨ p3) ∨ True) ∨ p1) ∨ p2) ∨ False))) ∨ (False ∧ p4)) ∧ p1) ∨ (p2 → True)))) := by
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
theorem thm_5_vars_49377820182575458827835251581 : (((p5 → (p1 ∨ (p4 ∧ (((p2 ∧ ((((p3 → p3) ∨ p3) ∨ (p2 → p3)) → p1)) ∧ (False ∧ p2)) ∧ p5)))) ∨ ((True ∧ False) → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114885872256280043952587648680 : (((p1 ∧ ((p4 ∨ ((p2 ∨ (p5 ∨ (False ∨ p1))) → True)) → (p2 ∧ p2))) ∨ (((False ∨ (p3 → False)) ∨ True) ∨ (p3 → p1))) ∨ (p1 → p4)) := by
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
theorem thm_5_vars_256029595737870990874496786044 : ((True ∨ p4) → (((((p5 ∨ p4) → ((((True ∨ p4) → False) ∨ (((p3 → p3) ∧ False) → False)) → p3)) ∨ ((p1 ∧ p1) ∨ p3)) ∧ False) ∨ True)) := by
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
theorem thm_5_vars_135729779704686844759676700148 : ((((True ∧ ((((True → True) ∨ False) ∨ p4) → (p4 ∧ (p2 ∨ True)))) ∨ p4) ∨ (p5 → (((False ∨ p3) ∧ p5) ∧ p1))) ∨ ((False ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148653107939123517026757172314 : (((((p4 → p4) → True) → (False ∨ (False ∧ True))) ∧ (False ∨ (p2 ∧ ((p2 → ((p1 ∨ p5) ∨ p4)) ∨ True)))) ∨ ((p2 ∨ (p1 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628836260626311267290646924871 : (((((p4 → (((True → p2) → ((p2 → p2) ∧ (p4 ∨ p3))) → (p2 → ((p1 ∧ p3) ∨ (p4 → (p3 → (p2 ∨ p5))))))) ∧ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177642463794248694758938731856 : ((((p3 ∨ (((True ∨ p4) ∨ ((p3 → True) ∧ True)) ∨ p5)) ∧ p4) ∧ p1) ∨ ((((p3 ∨ (p5 → (p3 ∧ p4))) → p5) ∧ (p2 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304920891389479779153036274182 : (p1 ∨ (((p3 → ((True ∧ p1) ∧ ((p2 → (p3 ∨ False)) → ((p2 ∨ p4) ∧ (((True → p4) → False) ∨ False))))) ∨ True) ∧ (True ∨ (p1 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706993737616894887078292783648 : (((((True ∧ (True → (p5 ∧ (p4 ∧ p3)))) ∨ p3) ∨ (True → ((True ∧ (p2 ∨ p4)) ∨ ((p1 ∨ (p2 ∧ p3)) ∧ (p3 → (p4 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22038061405707080009363682420 : (((((p1 ∨ ((p4 ∧ p2) → p3)) → p2) ∧ p5) ∨ (True ∨ ((p3 ∧ ((p3 → (False ∨ (p5 ∧ True))) ∧ p2)) → ((p5 ∧ p4) → True)))) ∧ True) := by
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
theorem thm_5_vars_142771370835193185591881166498 : ((p3 ∨ (((((False → p4) ∨ False) → p1) ∨ ((p3 ∨ (((p5 ∧ (p4 → p3)) → p1) ∨ (True → p1))) ∨ False)) ∧ p5)) → (p4 → (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
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
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157256501614576792543520514223 : (((((p1 → p4) ∨ (p4 ∧ False)) ∧ ((p2 ∧ (p3 ∧ ((False → p1) ∧ (p1 → p2)))) → p5)) → False) ∨ (((False ∨ (p4 ∧ p1)) ∧ p2) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39406533152408634401759694061 : (((p4 ∧ ((p2 ∨ (p1 ∨ (((((p2 ∧ (p5 ∧ ((False → p4) → False))) ∨ True) → p5) → p5) → p1))) ∧ (p2 ∧ (p2 ∧ p5)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258780048500696745451810449003 : ((True → False) → (((p2 ∨ ((((p1 ∧ p2) ∨ ((((p1 → False) → p2) → (p2 ∧ True)) ∧ p1)) ∧ p4) ∨ p3)) ∧ p5) → ((p2 ∨ p1) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
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
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h34 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h36 := h1 h35
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218295344084942518690734748532 : (((p4 ∨ p1) ∨ (p5 ∧ True)) → (((p5 ∧ p5) ∨ ((p5 ∨ (False → ((False → p4) → p2))) ∧ p4)) → ((p1 ∨ (True ∨ (p1 ∧ p2))) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54709391088528900805024168768 : ((((p4 ∧ (True ∨ (p1 → p5))) ∨ (True ∨ False)) → ((p1 ∨ (p3 ∨ (p1 → p4))) ∨ ((p1 ∧ False) ∨ ((True → True) ∧ (p2 → True))))) ∨ p3) := by
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
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111759449973741209828232830009 : ((((((p1 → p3) ∨ (((p3 ∧ (False ∧ p4)) → p1) ∨ (((p1 ∧ True) ∧ p1) ∨ (True ∨ p5)))) → p3) ∧ (p5 ∨ p4)) ∨ p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61046391992636455983304112680 : ((False ∧ (((((((True ∨ p1) ∨ p4) ∧ ((p4 ∧ p1) → (((p5 ∧ p4) ∨ True) ∨ p4))) ∧ (p1 ∨ True)) ∨ p4) ∨ False) → (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67796820182500082581490689022 : ((p2 → ((((((p3 ∧ True) → (False ∨ p2)) → (((p1 ∧ p5) → p4) ∨ (((p3 → True) ∧ p4) → p4))) → p2) ∧ (False ∨ p3)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743488074462825716304123477739 : ((((p5 → p4) ∨ (p1 ∧ (((((p4 ∨ p5) ∧ p5) ∧ ((False ∧ (p1 ∧ p3)) ∨ ((p3 ∧ p5) → p4))) → False) ∧ ((False ∧ p4) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130574593334199045942625202070 : ((((p1 ∨ ((((p4 → (True ∨ p3)) ∨ p1) → (p2 → p4)) → p2)) ∨ (True ∨ p3)) ∧ (p5 ∨ (True ∨ (p1 ∨ p1)))) ∧ (False ∨ (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172084586463371664158201108467 : (((((p3 ∨ False) ∧ p2) → (p1 ∨ (p4 → ((p5 → p5) ∧ True)))) → (True ∧ p5)) ∨ (False ∨ ((p4 → (True ∨ True)) ∨ (p4 → (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149087234060156936947119820369 : (((p1 ∧ (p1 ∨ p3)) → (p5 ∧ (((p3 ∨ p2) ∨ (p4 ∨ True)) → (p5 ∨ (p1 ∧ (p2 ∨ (p2 ∨ p3))))))) ∨ (True ∨ ((p3 ∧ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614252142557405001707785217924 : (((((((p1 → ((p4 → p4) ∨ True)) → (p4 → ((p4 ∧ False) ∨ (p5 → p3)))) ∨ ((p4 ∧ True) → p4)) → ((p5 ∧ p2) → False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53933953417825358790305621459 : (((True → (p5 ∧ ((((p2 → True) → p1) ∧ True) ∧ p3))) ∨ ((p2 → p5) ∧ (p5 → ((((True ∨ False) ∨ True) → (False ∨ p4)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350114741004689366395679775485 : (p4 → (((((True ∨ p1) ∨ ((p5 ∨ ((p3 ∧ False) → p3)) ∧ (True → (p3 ∧ p2)))) ∧ (True → p1)) → ((False ∧ (p3 ∨ False)) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726115867437769794922256195183 : (((((p2 ∧ p2) ∨ p5) ∨ ((((p5 ∧ (False → p5)) ∧ ((p1 ∨ (p3 ∨ p1)) ∨ ((p1 ∧ True) → p2))) ∧ True) ∨ (True ∨ (p3 → p3)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_787188382839840599805481901313 : (((p4 ∨ (True ∧ ((p1 ∨ ((p1 ∨ ((True → (p1 ∨ (p4 ∨ p5))) ∨ ((p2 → (p5 → (p2 ∨ (p5 ∨ False)))) → False))) → p2)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782796252059139583424646843384 : (((p3 ∨ (((p5 ∨ p1) ∨ (True ∧ (((((p3 ∧ (p1 → False)) ∧ (p2 → p4)) ∨ p1) → p2) ∨ ((p4 → p3) ∧ (True ∨ p5))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319719942856108482973403546100 : (p4 ∨ ((True ∨ (False ∨ ((False ∧ True) ∧ True))) ∧ (((p2 ∧ ((((p4 → (p3 ∨ True)) ∧ (p4 ∧ p2)) → p3) → p5)) ∨ (p1 → True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787098562988827625197686308291 : (((p4 ∨ ((p4 → p1) ∨ (p1 ∧ (((p3 → p2) ∧ p5) ∨ (((p4 ∨ (((p3 → (p1 ∨ p1)) ∧ (p5 → p1)) ∨ p3)) → p1) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197496681511119892495945380995 : (((p5 ∧ ((True ∨ p2) ∧ False)) ∧ (p2 → p2)) ∨ ((p2 ∨ (((p1 ∨ (p2 → True)) → (p4 ∧ True)) ∨ False)) ∨ ((True ∨ p3) ∧ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227910659517112007185728823726 : ((p2 ∧ (p3 → p4)) ∨ (p5 ∨ (((True → ((((((p1 ∧ p3) ∨ (p2 → (p4 ∧ p3))) ∨ p1) ∨ p2) → p2) → (p4 ∧ p2))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184347680351820695924575829748 : (((p4 ∧ ((p3 ∨ (p5 ∧ ((False ∨ True) → True))) ∨ p4)) → p3) ∨ (((p4 ∨ False) → False) ∨ (False → ((False ∧ (p1 ∨ p1)) ∨ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257183354605995324409930182477 : ((p2 ∨ p2) → (((((((((p4 ∨ False) ∧ ((False → False) ∧ ((p4 → (False ∨ p1)) ∨ p1))) ∧ p5) → p1) ∨ p5) ∧ p2) → p5) ∧ True) ∨ True)) := by
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



