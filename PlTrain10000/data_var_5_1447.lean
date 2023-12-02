variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862045769636821516405193631369 : ((((((((((p1 ∨ p5) ∧ p3) ∧ (p3 ∧ p1)) ∨ p4) → (((p3 ∨ p1) ∨ p3) → p4)) ∨ p1) ∨ ((p3 → (p2 ∧ p2)) → True)) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p1 ∨ p5) ∧ p3) ∧ (p3 ∧ p1)) ∨ p4) → (((p3 ∨ p1) ∨ p3) → p4)) ∨ p1) ∨ ((p3 → (p2 ∧ p2)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337697087576564529767721822635 : (p1 → (((p1 ∨ (((p1 ∧ p2) ∧ (p1 ∨ (((p4 ∧ p5) ∨ p5) ∧ p2))) → p2)) → (p5 ∧ p5)) → ((p2 ∨ p5) ∨ (p5 ∧ (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ (((p1 ∧ p2) ∧ (p1 ∨ (((p4 ∧ p5) ∨ p5) ∧ p2))) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178290263958700453425983998187 : (((False ∨ (True ∨ ((p2 ∧ p5) ∨ ((p2 → p5) → p1)))) ∧ (False ∧ p4)) ∨ (p2 ∨ (p4 ∨ (((((p3 ∨ p3) ∧ p3) → True) ∧ p5) → p5)))) := by
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
theorem thm_5_vars_302543751763366892640608103670 : (False ∨ (False ∨ (p4 ∨ (p1 ∨ (p1 ∨ (((True ∨ True) ∨ p2) ∨ ((p3 ∧ p1) ∨ (p2 ∧ ((p3 → p5) ∧ (True ∨ ((p5 → p4) ∧ p4))))))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185384869600630976302727241594 : ((p5 ∧ ((p4 → False) ∨ ((((p5 ∨ p4) ∨ p5) ∨ False) ∧ True))) ∨ ((p4 → (((True ∧ p3) ∧ p5) → p4)) ∨ (((p2 → p5) ∧ p4) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312966986265261292299525258978 : (p3 ∨ ((((p5 ∨ ((p1 ∧ p3) ∧ ((True ∧ ((p1 → p5) → (True → p1))) ∧ (p5 → p2)))) ∨ (p2 ∧ (p2 → (True ∧ p3)))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217452587083837634473741042943 : (((p4 → (p3 → True)) ∨ p2) → (False ∨ (p5 ∨ ((p1 ∧ (((p4 → p3) ∧ p4) ∧ (p1 → p3))) → (((p2 ∧ p4) → (True → p3)) ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257701552488535594502348830060 : ((p3 ∨ p3) → ((p5 ∨ (p4 ∧ p1)) ∨ (p2 → (p5 → ((p4 → ((p2 ∨ ((p2 ∧ ((p2 → True) → p3)) → (p3 → False))) ∧ p5)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668374529316969685787988830615 : ((((p5 → (p5 → (p2 ∨ ((p2 → ((True ∨ False) ∨ (p1 ∧ p3))) → ((False ∨ p5) ∧ (p3 ∧ (p1 → True))))))) ∧ ((p3 → False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167288669533931171911055031011 : ((((p2 ∧ ((((p5 ∧ p4) → (p1 ∨ False)) ∧ p2) ∨ (True ∧ (p5 ∧ p4)))) ∨ True) → False) → ((p2 → p2) → (p5 ∧ ((p3 ∨ p3) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ ((((p5 ∧ p4) → (p1 ∨ False)) ∧ p2) ∨ (True ∧ (p5 ∧ p4)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∧ ((((p5 ∧ p4) → (p1 ∨ False)) ∧ p2) ∨ (True ∧ (p5 ∧ p4)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42923983968704265706549948209 : (((p4 → ((((True → ((p3 ∧ ((False ∨ p1) ∧ False)) ∧ ((p4 → False) ∧ p5))) → True) → (p5 ∧ ((True ∧ p3) ∨ False))) ∨ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649634735429782866279749334871 : (((((((p5 ∨ p2) ∨ (p1 ∨ p3)) ∨ (True → (((p2 → (p3 ∧ p3)) → (p1 ∧ (p4 → p5))) ∧ p5))) ∨ (False ∨ True)) ∧ (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178906177780885171281329619567 : (((p4 ∨ p1) ∧ (p3 ∧ ((p4 ∨ ((p1 → p5) → p4)) ∧ (p4 ∨ p4)))) ∨ (p3 → (((p1 ∨ False) → (((p2 ∧ p5) ∧ p4) → p4)) ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196936243348486568822319778645 : ((((p3 → (False ∧ (False ∨ p4))) ∧ p4) ∨ p4) ∨ (((p4 ∧ p1) ∧ (False ∧ (((p4 ∧ p3) ∨ (False → (p3 ∨ p3))) ∧ p3))) → (p1 ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h9.left
  let h13 := h9.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223397094265719784292145910339 : ((True ∨ (True → False)) ∧ (((p2 → ((False ∨ ((p5 → True) ∨ p1)) ∧ ((False ∨ True) → (p4 → p5)))) → ((True ∧ (p5 ∧ p2)) ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_136118022249543068551655703931 : (((p4 ∧ (((p2 ∧ (p4 → False)) ∨ p3) ∨ p4)) ∨ (p2 ∧ (((p3 ∧ (p2 ∨ (True ∨ p1))) → (p2 → True)) ∧ p3))) ∨ (False ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730164958554051770496723379956 : (((((True → True) → True) → (((p5 ∨ False) ∨ ((p5 → (False ∨ p3)) ∨ p5)) ∨ (p2 → (((True ∨ (False ∧ (p1 → p2))) ∨ p1) → p2)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60432461031289025373548891506 : (((p4 → p4) → (((p1 ∧ (p1 ∧ (p1 ∧ True))) → False) ∨ (((p5 ∧ (((False ∨ p3) → ((p2 → p1) → False)) ∧ p4)) → True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782411510311744713659792243074 : (((p3 ∨ (((((((p1 ∧ p3) ∨ ((p4 → p5) ∧ (p1 → p3))) ∧ (True ∧ (True ∨ True))) → False) ∧ (True → p1)) ∧ (p2 ∧ p5)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_47504474402452376343361292980 : (((p1 ∨ (p1 → ((((p3 ∨ False) ∨ p4) ∨ ((p5 ∧ False) ∧ (p5 ∨ p2))) ∧ (False → ((p3 → p4) ∨ (True → True)))))) ∨ (False → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178042028371928821419977078930 : ((((((p4 ∨ p4) → ((False ∧ True) ∧ p3)) ∨ (True ∧ p5)) ∧ p2) → False) ∨ (p5 → (((((p5 ∨ True) ∧ p4) ∧ p1) → True) ∨ (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709726508296536548866831759494 : ((((True → (p4 ∨ (((True ∨ False) ∨ True) → p2))) → ((p5 ∨ (((p1 → p2) ∧ (p4 ∨ p5)) ∨ (((p5 ∧ p5) ∨ p1) ∧ p5))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742366861860691362402525608645 : ((((p1 → p4) ∨ ((p2 ∨ ((((p5 ∨ (p4 ∨ p1)) ∨ p3) ∧ (p1 ∨ True)) ∧ ((p4 ∧ True) ∨ ((p2 → (p3 ∧ False)) → p2)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135948017139818561672608007530 : ((((p4 → (p1 ∧ ((True → p1) ∨ True))) → (p4 ∧ p2)) ∧ (((p4 → (p1 ∧ p4)) ∨ ((p4 ∨ p1) ∧ False)) → p3)) ∨ ((True ∧ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141459780971207771640999901773 : ((((p3 → p4) → False) ∧ (((((p2 → (((True ∧ p4) → (p3 ∨ (p3 → p3))) → p5)) → p3) ∨ p5) → False) ∨ p1)) → ((p4 → p1) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p3 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (((p2 → (((True ∧ p4) → (p3 ∨ (p3 → p3))) → p5)) → p3) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h8
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h6
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254333138137644137769921528203 : ((p2 ∧ p4) → ((False ∧ (True ∧ (True ∧ ((((p3 ∧ (False ∨ p1)) ∨ False) → (p2 ∨ ((p3 → (False ∧ p5)) ∧ p1))) → (False ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230111919391016781660613269034 : (((p3 ∧ p3) ∧ p1) → (((p5 ∨ p5) ∨ ((((False ∧ p3) → (p5 ∨ p4)) ∧ (p5 ∧ ((p5 ∨ p2) ∨ p1))) ∨ ((p4 ∧ p2) ∨ p2))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325086941162993125515995929848 : (p5 ∨ ((False → p1) → (((((False ∨ ((p1 → p4) ∨ (p1 ∨ (p5 → (False → p5))))) ∨ False) ∧ p4) ∨ ((True ∧ True) ∧ (p3 → p3))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342966006320968450390995411576 : (p2 → ((((p3 → p5) ∧ True) ∧ True) ∨ ((p3 ∧ p3) ∨ ((p2 ∧ ((p2 ∧ (False ∨ (True → p3))) → (False ∧ False))) ∨ ((p3 ∨ True) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197132912586130341791104309476 : (((p5 ∨ ((False ∧ (p3 ∧ p1)) ∧ p2)) ∨ False) ∨ (((p1 → True) ∧ ((p4 ∧ (((p4 ∨ p1) ∧ ((False ∧ True) ∨ False)) ∨ False)) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330586055205034922762588800891 : (True → (p5 ∨ (p5 ∨ (((p4 → ((p2 ∨ p2) → (((True ∨ p3) → False) → (((p2 → False) ∧ True) → (p1 → p4))))) → p4) ∨ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_252289348161724281206023810186 : ((p4 → p5) ∨ ((((p3 ∧ p2) ∨ (((True → p5) ∨ p2) → p1)) ∧ p1) ∨ ((p2 → ((False ∧ p3) ∨ (p2 ∨ True))) ∨ ((p3 → p2) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158147674923265557062194545262 : (((p1 ∧ ((p2 → p4) → p1)) ∨ ((((p5 ∧ p3) ∧ (p5 → True)) ∨ True) ∨ (p3 → (p2 → p3)))) ∨ (p1 → ((p3 → (p4 → p3)) ∧ False))) := by
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
theorem thm_5_vars_307206273065465158304149582604 : (p1 ∨ (p1 ∨ ((p1 ∨ ((((p2 → p3) ∧ True) → False) ∧ p3)) → ((p2 ∨ (((True → (p5 ∨ (p4 ∧ False))) ∨ p5) ∧ p2)) ∨ (p2 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42996523581374478341448804519 : (((p5 → (p4 → ((p4 ∨ ((p4 → (p1 → (((p3 → (p2 → p1)) ∧ (((p1 ∨ p1) ∨ False) ∨ p5)) → p1))) ∨ p3)) → p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780073390719729919049986513513 : (((p2 ∨ (((((True ∧ p1) → p1) ∧ ((((False ∧ ((((p2 ∨ p5) ∨ p3) ∧ p4) ∨ False)) ∧ True) ∨ p4) ∨ p4)) ∨ p4) → (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60321005508132268154251532977 : (((p1 → p5) → (True ∧ (((p1 ∨ p5) ∧ ((p1 ∨ True) ∧ (p2 ∨ p5))) ∨ ((p1 ∧ (((p4 ∨ p2) ∧ (p2 → False)) ∨ p4)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39567678843843506729055181212 : (((p1 ∨ ((((p2 → ((p5 ∧ p3) → p1)) ∧ ((p2 ∨ p1) ∨ p3)) → p3) ∧ ((((p5 ∨ False) ∧ False) ∨ (False ∨ p2)) ∧ True))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112920412301805535153423429016 : ((((p4 → True) ∨ ((p3 → False) ∧ ((p3 ∧ p5) ∧ (False → ((p1 → p5) ∨ (((True → p3) ∧ p4) → (False → False))))))) → p4) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115213897616683496439270058588 : (((p4 ∨ ((((True → (p1 → p4)) ∨ p1) ∧ p3) ∧ p1)) ∧ ((((True ∧ (p4 ∧ p5)) ∧ ((p1 ∧ p3) ∨ p5)) ∨ p5) → True)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43889638032792338121637234170 : ((((p1 ∨ (p4 ∨ ((((p3 ∨ p3) ∨ p5) ∧ (p2 ∧ p5)) ∨ ((p5 → (p5 ∧ p3)) → ((p4 ∨ False) ∧ False))))) ∧ (p2 ∧ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704833417036838355854367456201 : ((((False ∨ ((p3 ∨ p5) ∧ (p4 ∧ ((p1 ∨ True) ∧ True)))) → (p5 → (True → ((((p3 ∨ p3) ∨ ((p4 → p5) ∧ p3)) → p1) ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45764387691859785044957198471 : (((False → ((False ∧ p2) → ((((False ∧ True) ∨ False) ∨ (((p5 ∧ p1) ∧ True) ∧ (((p1 → p5) ∨ (p1 → p2)) → p4))) ∧ p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259614626566553031989304478802 : ((p1 → False) → (((p1 → (p3 ∧ (False ∨ (p5 ∨ ((p5 ∨ (p3 ∧ p1)) → (((True ∨ p1) → p2) ∧ p5)))))) ∨ ((p4 → p5) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798246291850697527449641971319 : (((p1 → (((((p5 ∨ True) ∧ ((p3 → (p3 ∨ p5)) ∧ (p3 ∧ p3))) ∧ (p2 ∧ False)) ∨ p2) ∨ (p1 ∨ ((False → (p4 ∨ False)) → p1)))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48136403744279233453733005581 : (((((p2 ∨ p2) → p5) ∨ (((p5 ∨ p5) ∨ (p3 ∧ p3)) ∧ ((p2 ∨ (((p3 → p1) ∧ p4) ∨ (False → p4))) → p2))) → (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257057072932665676925096707259 : ((p2 ∨ False) → ((((p4 → p1) → ((p2 → p1) ∨ ((p1 → (True ∧ ((((p3 ∨ (p1 ∨ p3)) ∧ True) → p5) ∧ True))) ∨ p2))) ∨ p5) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43366368334231487177645538148 : (((((((p2 ∧ (p4 ∨ ((p4 ∧ (False → False)) → p3))) ∨ ((False ∨ (True ∨ (p4 → p4))) ∧ False)) → p5) → (p2 ∨ p3)) ∨ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300121868737557704719089883887 : (False ∨ ((((p1 ∧ p4) ∨ False) ∨ (p3 ∨ (((((p3 ∨ (p1 ∧ p5)) → False) ∧ (p5 ∨ p3)) → ((p1 → p5) → p4)) ∨ p1))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148466458378270844380542709079 : ((((p1 ∨ True) → ((((True ∨ p5) ∧ p4) ∨ (p1 ∨ p3)) ∨ p1)) ∧ (p3 ∧ (p4 ∧ (p2 ∨ (p1 → p4))))) ∨ ((False ∧ False) → (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49500081493213315022046443812 : ((((p3 ∧ (p4 → ((((True ∨ ((p3 ∨ (False ∨ p2)) ∧ p1)) ∧ ((p5 ∧ p4) ∧ p2)) → False) ∨ p5))) → True) → ((p4 ∨ p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114391337900629243889399818448 : (((((p4 ∧ (p4 → (False ∧ (False ∧ ((p2 → p1) ∨ p2))))) → True) ∧ (p3 ∨ (True → p3))) ∨ (p4 ∧ ((p3 → p2) ∨ p4))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56640626280297220717454626756 : ((((True ∨ p5) ∧ p2) ∧ ((p3 ∧ ((((p4 → p4) ∧ p3) → ((False ∨ (p2 ∧ p5)) ∧ p2)) ∧ (p3 → p2))) ∧ ((p5 → p3) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259659945648909844226617370344 : ((p1 → False) → (p3 ∨ ((p3 ∨ ((p2 → (p1 → (p2 ∨ p2))) ∨ p5)) → (p1 → (p3 ∨ ((((False → True) → (p5 → p1)) ∧ p3) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655076123491640775653311324651 : (((((p5 ∧ ((((p3 → ((p4 ∧ p5) ∨ True)) ∨ (False ∧ (False ∨ p1))) ∧ p3) ∧ (True ∨ (True → (p3 ∨ True))))) → p4) ∨ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191834668140941356876337377371 : ((p3 ∨ (((p4 → (p3 → False)) → p3) ∧ (False ∧ False))) ∨ (((False → ((((p4 ∨ False) → ((True ∧ p1) → p4)) → p4) → False)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201772746959909133414351060985 : (((((p3 ∨ p5) ∧ False) → True) ∨ p4) ∧ (p1 ∨ ((((True ∨ p5) ∧ (((p3 ∨ p1) → ((True ∧ False) ∨ True)) → (p2 → p1))) ∨ True) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601231673720920227962519539682 : ((((p2 ∧ ((p2 → (True ∨ (((p1 ∨ ((p3 ∨ False) → p4)) ∧ p5) ∨ (p4 → ((p4 → (p3 ∧ p2)) ∧ (p2 → True)))))) → p3)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251134623639837917239338057782 : ((p2 → False) ∨ ((((p5 ∧ (p3 ∨ p3)) ∨ (True ∧ (p4 ∧ (p5 ∨ p5)))) ∧ True) → (True → (p1 ∨ ((p5 ∨ p4) ∨ (p1 ∨ (p1 ∧ p4))))))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58250430398122050339188786576 : (((p5 ∧ p1) ∧ ((True ∧ (((p1 ∨ (p2 ∧ p2)) → p2) → (True → False))) ∨ (p2 ∧ ((p5 ∨ ((p5 ∧ (p3 ∨ p5)) → True)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198067321510969651419922674398 : (((False ∨ p5) ∨ ((p4 ∧ (p1 ∧ False)) ∧ False)) ∨ ((((p4 ∧ False) ∨ p1) → True) ∨ (p2 ∧ (p1 → ((p3 ∨ (p1 → p5)) ∧ (p2 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664307760017417655085101566299 : ((((p2 ∨ (((((p1 → (p4 ∧ ((True → False) → False))) ∨ (p4 → (p1 → (p4 ∧ p3)))) → p1) ∨ p3) ∧ (True ∨ False))) → (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158913287064953007796477320515 : ((p1 ∨ ((p5 ∧ (p2 ∨ True)) → ((((p4 ∧ (p4 ∧ (True ∨ True))) ∧ p3) ∧ p4) ∨ (p3 → p2)))) ∨ (p4 ∨ (True ∨ ((p5 ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231773523043611669303824270448 : (((p3 ∧ p4) → p4) → ((p2 ∨ (p5 ∨ p2)) ∨ ((p3 → p2) ∨ (((p1 ∨ (((False → p5) → p3) ∨ ((p2 ∨ p3) ∨ p4))) ∧ False) → True)))) := by
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
theorem thm_5_vars_248232277347820274246872849950 : ((p2 ∨ p1) ∨ ((p3 ∧ p3) → (p1 → (((p5 → (((((p4 ∨ (True ∧ p5)) ∨ p3) ∧ (p1 ∧ (False → p4))) ∧ True) → False)) ∨ p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258046591533035118977485647665 : ((p4 ∨ p2) → (((((((p1 ∧ (p1 ∧ (p3 ∧ p2))) ∧ p3) → ((p2 → (p4 ∨ (p4 ∨ p2))) ∧ p3)) → p4) ∧ p2) → False) ∨ (p3 → p3))) := by
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
theorem thm_5_vars_347231847743877557157626489435 : (p3 → (((p4 → False) ∨ (p3 ∧ ((False ∨ p1) → ((True ∧ p1) → False)))) → ((p2 ∨ (False ∨ p5)) ∨ (True ∨ (((p5 ∨ p1) ∧ p2) ∨ False))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39911757234176817636429753957 : (((p3 → ((((False → ((True ∨ ((((p1 → True) ∧ p2) ∧ ((p1 ∧ p2) ∧ p2)) ∨ p3)) → p5)) → (p5 ∧ True)) → p4) → p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42348227201362608997217614266 : (((p3 ∧ (((((True → p1) ∧ False) ∧ (False ∧ p1)) ∨ (p2 ∧ p2)) → (p5 ∨ ((p1 ∧ (p1 ∨ p4)) ∨ ((p4 → p4) → p4))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345487439168913579377081528691 : (p3 → (((((p1 → ((p1 → (p4 ∧ p1)) ∧ (p3 ∨ (True → (True → p3))))) ∨ False) → (False ∧ p4)) ∨ (((p3 ∧ p3) ∨ p2) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_123314324604431954330983827844 : ((((((True → p5) → p3) ∧ (((True ∨ p3) ∨ True) ∧ (False → (p4 ∧ p3)))) ∨ (p4 → p5)) ∨ (True → (p5 → (True → p5)))) → (p4 → p4)) := by
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
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261617209101941664217576755653 : ((p5 → p5) → ((((p4 → ((p1 ∨ ((p5 ∨ p1) ∨ (p5 ∨ ((p1 ∧ (p2 → False)) ∧ p1)))) ∨ (True ∨ p1))) ∧ (p2 ∧ True)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127774721435433037844030888800 : ((True → ((((((p2 ∨ p2) ∨ p5) ∧ False) → True) ∧ ((False ∨ (p2 ∨ p3)) ∨ (p1 → True))) → (((p2 → p2) ∨ False) → False))) → (p4 ∧ False)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p2 ∨ p2) ∨ p5) ∧ False) → True) ∧ ((False ∨ (p2 ∨ p3)) ∨ (p1 → True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 → p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : (((((p2 ∨ p2) ∨ p5) ∧ False) → True) ∧ ((False ∨ (p2 ∨ p3)) ∨ (p1 → True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h13
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : ((p2 → p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h19 := h16 h17
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50206367504626355257231239747 : (((((((p5 ∨ p2) → (p1 ∧ ((p5 ∧ (p4 ∧ (p4 ∨ (p4 → p4)))) → p5))) ∨ False) → p4) ∨ False) ∨ (((p5 → p2) → True) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37792851924716481143639714724 : (((((p5 ∨ p4) → ((((p4 ∨ (p3 → (False ∧ p4))) → (True ∧ p4)) → (p2 → (p3 ∧ (p1 ∨ (p3 ∨ p4))))) ∧ p2)) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347706287126622957518844204756 : (p3 → (((p4 ∧ True) → p4) ∧ (((p3 → ((((((p5 → p2) ∨ (p1 → p4)) ∧ p5) ∧ p4) ∨ p3) ∧ False)) ∨ False) ∨ (False → (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309844428177078249831196711624 : (p2 ∨ ((((False → (p5 ∧ (p5 → p5))) → ((p2 → p2) ∨ (p1 → False))) → (p3 ∧ ((p4 ∧ False) ∧ True))) → (((p5 ∨ p5) ∨ p4) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p5 ∧ (p5 → p5))) → ((p2 → p2) ∨ (p1 → False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((False → (p5 ∧ (p5 → p5))) → ((p2 → p2) ∨ (p1 → False))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h9
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41802078982088212740374418649 : ((((p2 ∨ ((False ∨ False) ∧ False)) → (((((False ∨ (p5 → p5)) ∨ (True → p4)) → p5) ∧ p5) ∨ (((True ∧ p5) ∨ False) ∨ p5))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39333853279822931332787580373 : (((p2 ∧ ((p2 ∧ ((p1 ∧ (p2 ∨ True)) ∧ (p5 ∧ p3))) ∨ ((True ∧ ((p5 ∧ p5) ∧ (p1 ∧ True))) ∧ ((True ∧ p5) ∧ p2)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191146218858976608106711201527 : ((((True → p3) ∨ p5) ∨ (p2 ∨ ((p1 ∧ p3) → p5))) ∨ (((p2 ∧ p3) → ((False ∧ p5) ∨ ((p4 → False) → p2))) ∨ ((True → p2) → p2))) := by
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
theorem thm_5_vars_41333347715114515618554192520 : ((((((p2 → p4) ∨ (p4 ∨ (False ∧ ((p2 ∨ (p4 ∨ p1)) ∧ (p1 ∧ p4))))) ∨ p3) ∨ (((p2 → p5) → (p5 → p3)) → True)) ∨ False) ∨ p1) := by
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
theorem thm_5_vars_133973113552223238992505968326 : (((((((p2 ∨ p4) ∧ (((((p2 ∧ True) ∨ p5) ∧ ((p4 → p4) ∧ True)) ∨ p2) ∧ p3)) ∧ p3) ∧ p1) ∧ True) ∨ True) ∨ ((p1 ∧ True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172270425991243660617102343152 : ((((((False ∨ p3) ∨ True) → p5) ∨ (p4 ∨ p1)) ∨ (p5 ∧ ((p2 ∧ p4) ∨ p3))) ∨ (False → (p3 → (p3 → ((p4 ∧ p2) ∧ (True ∨ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124480472774092282129953496522 : (((((True ∧ p3) ∨ (True → p3)) ∧ p4) ∧ (((p5 → ((True ∧ True) → (True ∨ p2))) ∨ p3) ∨ (p4 ∧ ((p4 ∧ p3) → True)))) → (True → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h20 := h16 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h26 := h16 h25
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164868843781583849378815331316 : (((p4 ∨ (p5 ∧ (((p3 → (((True ∨ p4) → (p4 ∧ p3)) ∧ False)) ∨ p3) ∧ p1))) ∨ True) ∨ (((False ∧ (p2 ∨ (p3 ∧ False))) ∧ p2) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114703755636446922755529474277 : (((((False ∨ ((p2 ∨ p1) ∧ (p4 → ((False ∨ p4) ∨ (False ∧ p4))))) → p2) ∨ p3) → ((p1 ∧ (p5 ∨ (p4 ∧ p4))) ∧ p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811135119125517994466333119529 : (((p5 → (p2 ∧ (False ∧ (p4 → (p2 ∨ ((p1 ∧ (((((p4 ∧ p4) ∧ p1) ∨ p4) → ((p3 → p5) → p1)) ∧ False)) ∨ (p1 → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1548129593801340436127719370 : ((p4 ∧ ((True → ((((p4 → (False ∧ ((p2 → p3) ∧ False))) ∨ ((p5 → (p4 ∨ p5)) ∨ p4)) → p4) → False)) ∨ p4)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304718755584414079652365710872 : (p1 ∨ ((((p5 ∨ (((True → p2) ∧ ((p1 ∧ p1) ∨ (p1 → (False ∨ False)))) ∨ (False ∧ True))) ∨ p3) → ((p2 → p3) ∨ p3)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247799310965664500686094532598 : ((p1 ∨ p1) ∨ (((p2 ∧ (p4 → p4)) → True) ∧ ((False → (False ∨ p5)) → (((p1 ∨ (p3 ∨ ((p3 → p1) ∧ p3))) ∨ (True ∨ p1)) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43334212122741556377316722312 : (((((((True ∨ (((True ∧ (p1 ∨ (((False → p3) ∨ p2) ∧ p1))) ∨ False) ∨ False)) ∨ True) ∨ (False ∧ (p4 → p5))) → True) ∨ p2) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266084518592520421769309693273 : (True ∧ (p2 → (((False ∨ (p3 ∨ (True ∧ p2))) → (p4 ∧ p4)) → (p4 ∧ (((True → (p2 → p5)) ∧ True) ∨ (p4 ∨ ((p4 ∨ p4) ∧ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ (p3 ∨ (True ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ (p3 ∨ (True ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781249862750807812995704380869 : (((p2 ∨ (True ∧ ((p3 ∧ ((((p1 → p2) ∧ (p4 ∨ p5)) ∨ p1) → p3)) ∨ (((False ∨ ((p5 ∧ p5) ∨ False)) ∧ (p5 ∨ p5)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184476374607584403464026524364 : (((((p5 ∧ p3) ∨ (p3 ∧ (p4 ∨ p4))) ∨ True) ∨ (p3 ∧ p2)) ∨ (((p4 ∨ (p4 ∧ p5)) ∨ ((p1 ∧ False) ∧ p1)) ∨ (p3 ∧ (p5 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323514734260131860283863620523 : (p5 ∨ ((True ∧ (((((p3 ∨ p4) → ((((p1 ∨ p3) ∨ p5) → p3) → p5)) → p3) ∨ p1) ∨ (p1 → (p5 ∨ p3)))) ∨ ((p5 → True) ∨ p4))) := by
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
theorem thm_5_vars_711213323912908198924388814233 : ((((p3 ∧ (p3 → ((p3 → p3) → True))) ∧ ((p4 → (((((p3 ∨ (((False → p5) ∨ p2) ∧ False)) ∨ p2) ∨ p2) → False) ∧ p1)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198037552542918547625977229768 : (((p1 ∧ False) ∨ ((p1 → (False ∧ p3)) ∨ p5)) ∨ (p5 ∨ ((((False → (p2 ∨ p2)) → (p4 ∧ p2)) → p4) ∨ ((False → p4) ∨ (p4 → p5))))) := by
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
theorem thm_5_vars_165839041631370236118204059899 : ((((p4 → True) ∧ False) ∨ ((p4 ∧ (p5 ∧ False)) ∧ (((p2 → p2) ∨ (p3 ∨ p2)) ∧ p3))) ∨ (False → (p1 ∨ ((p2 ∨ True) → (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148150291048192046617361966608 : (((p3 ∨ ((p1 ∨ False) ∨ ((((p5 → (False ∨ p5)) ∧ p3) → ((False → p1) → p5)) ∨ p2))) → (p5 ∨ p5)) ∨ ((p1 → (p4 ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233129900448714717610067952653 : ((p5 ∧ (p1 ∧ True)) → ((((((False → p2) ∨ (p2 → False)) → (((p3 ∨ (p2 ∧ p2)) ∧ p4) ∨ True)) ∨ (p2 ∨ p5)) ∨ (True → p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



