variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204301671107680698062949220480 : (((True ∧ (p4 ∧ (p2 ∧ p5))) ∧ False) ∨ ((p1 ∨ p5) ∨ (True ∨ (((True ∨ ((p1 ∧ ((p1 ∨ (False ∨ p1)) → p3)) ∧ p1)) ∨ p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136316078281589106425353824928 : ((((p4 → (p1 → False)) ∨ p4) ∧ ((False ∨ p2) ∧ ((((p3 → (p5 → (p5 → (p5 → p3)))) ∧ p5) ∨ p5) ∨ True))) ∨ (True ∨ (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351233739007015592771842188154 : (p4 → (((p1 ∨ (((p5 → ((p3 ∨ (True ∧ p1)) ∧ p3)) ∨ (p3 ∧ True)) ∧ p3)) ∨ (((False ∧ p5) ∧ True) ∨ p4)) ∨ ((False ∧ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258803008229287150184297064472 : ((True → False) → (p2 ∧ ((p4 ∧ (((((p5 ∨ False) ∨ False) ∧ (p3 ∨ (p3 ∧ (p1 ∨ p1)))) ∨ (p4 ∧ (p3 ∨ p2))) ∨ (p1 ∧ p4))) ∨ p1))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49007201602819630187145271530 : (((((p5 → ((((p5 → p2) ∨ p1) ∨ ((((p4 ∨ p2) ∧ p1) ∧ True) ∧ True)) ∧ (p3 → p5))) ∧ p1) → p5) ∨ ((True → p3) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351620255018627553246420788199 : (p4 → ((p1 → ((p1 → p4) ∧ (((p4 → ((p2 ∨ (True → p2)) ∨ True)) → False) ∨ True))) ∧ (((p5 → (False ∨ p4)) → False) → (p5 ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → (False ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299202096612590369315769821785 : (False ∨ ((((p4 ∧ (((p5 ∧ (p4 ∧ p3)) → p3) → ((p4 → False) → (p2 → ((False ∨ p3) ∨ (p3 ∧ p5)))))) → False) ∧ (p2 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122851034263484537057305533065 : (((((p3 → p2) ∧ ((((p4 → p3) → (p1 ∧ p5)) ∨ (p4 ∨ p1)) → False)) → ((True → p3) ∧ True)) ∧ ((p1 → p2) ∧ p5)) → (p2 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41571420550054040013922433042 : ((((p2 → ((((False ∧ False) → p3) ∧ p4) → (True ∧ True))) → (((False ∨ (((p4 ∧ p1) → True) ∧ p1)) → (p2 ∨ False)) ∨ True)) ∨ p5) ∨ p1) := by
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
theorem thm_5_vars_165064336287960050286301636433 : (((p1 ∧ (False ∨ ((((p4 ∨ (p1 → (p4 → p1))) → p5) ∨ p5) ∧ (p1 → True)))) → False) ∨ (False ∨ (True ∧ (True ∨ (True ∨ (True → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_176669601091259760011910591494 : (((((p1 → p1) → p5) ∧ p5) → (p2 → ((p1 ∧ (p2 → p3)) ∨ p2))) ∧ (((p4 ∧ ((p2 → False) ∧ True)) → (False ∨ p4)) ∨ (p4 ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709464595504431694766359883579 : ((((p3 ∧ ((False ∧ (False ∧ p1)) → (p4 ∧ p2))) → (((((p5 ∨ p4) ∨ ((p4 → p1) → (p3 ∨ (p5 ∧ p1)))) → p5) ∨ p2) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115216242801594167106077485673 : (((True → (((False ∨ p2) ∨ p3) ∧ ((p4 ∨ p1) ∧ p5))) ∧ ((p4 ∧ ((p1 → p5) ∧ (False → ((p3 → False) → False)))) ∧ False)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115203109416098730911248634690 : (((True ∧ (p1 ∧ ((((p1 → p5) ∨ True) → p5) → p5))) ∧ (True ∧ ((p1 ∨ ((True → (p5 ∨ False)) → (p1 ∨ p1))) ∧ False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245782961069660742171267586578 : ((p3 ∧ p3) ∨ ((((((False → (p3 ∨ (p3 ∧ (p3 ∨ (p3 → (p3 ∨ False)))))) → True) ∧ p1) ∨ (False ∧ p1)) ∧ p4) ∨ (p5 → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264058910526166173042653152108 : (True ∧ ((((True ∧ p4) ∨ (p5 ∧ (p5 ∨ (p5 ∧ p3)))) ∧ False) ∨ ((False → p2) → (p4 → (((p1 ∨ False) ∧ ((False ∨ p1) ∧ p5)) → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780810501681666368186386683116 : (((p2 ∨ ((((p2 ∧ p1) ∨ p2) ∨ p2) ∨ (((p4 → (p5 ∧ ((p4 ∨ (p5 ∨ (True ∨ (p1 ∧ (p2 → False))))) → p2))) ∨ True) ∧ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197028951476855576174881755899 : (((((p4 → p4) ∨ p2) → (p2 ∨ False)) ∨ p3) ∨ (p4 → (((((p3 → False) → p2) → False) ∧ (p4 ∧ p1)) ∨ (((p3 ∧ False) ∧ True) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105757500645193375148214656763 : (((p4 ∨ (((p3 → p4) → ((p1 ∧ (((p3 ∧ p1) → p3) ∧ p3)) ∧ p1)) ∧ p4)) ∨ (((False ∧ (False ∨ p3)) ∨ True) → True)) ∧ (True ∨ p3)) := by
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
theorem thm_5_vars_350939640418267103924789826060 : (p4 → ((((p3 ∧ ((p4 → p5) → (((True ∧ (p3 ∧ False)) ∧ p1) ∨ ((p5 ∨ p5) → (p4 → p5))))) ∨ p2) ∨ (True ∨ p5)) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656743166807826646921833338263 : ((((((p1 → p2) ∧ (p4 ∧ (False ∨ p3))) ∨ ((p5 → ((((p2 ∨ True) ∧ p1) ∨ False) ∧ p2)) ∨ ((p5 → p3) ∧ False))) ∨ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144681974139259094537813921790 : (((True → (((p3 → (((p4 ∧ p5) → p1) ∧ (p4 → (p3 ∧ False)))) ∧ p3) ∧ (p2 ∨ False))) → (p4 → p2)) ∧ (((p1 → p4) ∧ p3) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923612090780582684248150994737 : (((((((p3 ∨ p2) ∨ False) → True) ∧ ((False → (p5 → p2)) → p2)) ∧ ((((False ∨ p1) ∧ (p3 ∨ p4)) → (p2 → p5)) ∧ (True → p3))) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (False → (p5 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h8
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311043368866331941525776839437 : (p2 ∨ ((p4 ∧ False) ∨ (p5 → ((((p4 ∨ p3) ∨ (p4 ∨ (((p5 ∧ False) → True) ∨ ((False → p1) ∧ p4)))) ∨ (p2 ∨ p2)) ∨ (p4 ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45089891147257304106418941743 : ((((p4 ∧ p2) → (p3 → (True → (p1 → ((True ∨ ((((p2 ∧ (p3 ∧ True)) ∧ (p3 ∨ True)) ∧ p4) ∧ (p3 ∨ p1))) ∨ p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184389903372738826696586921824 : (((p3 → ((p5 ∧ (False ∨ p4)) ∧ ((p3 ∨ False) ∨ p3))) → p4) ∨ ((True ∨ (p2 ∨ (p4 ∧ (p3 ∨ ((p1 ∨ p2) ∨ p3))))) ∨ (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67497342802519736610979683215 : ((p1 → (((((((p4 ∨ p2) ∨ True) ∧ p1) ∨ p3) → True) ∧ p2) ∨ (p3 ∧ ((((p5 → p2) ∨ True) ∧ (p1 → False)) ∧ (True ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312502612469104311930083916863 : (p2 ∨ (p5 → ((p3 → (p2 ∨ p1)) ∨ ((((((p2 ∧ False) → ((False ∨ (p1 ∧ p4)) ∧ p3)) ∨ p2) → ((p3 ∧ True) ∧ p4)) → p4) ∨ p4)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 ∧ False) → ((False ∨ (p1 ∧ p4)) ∧ p3)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40973692340366283456849405754 : ((((((p1 → True) ∨ p3) → ((((True ∨ ((p1 ∧ p2) → p3)) ∧ (p4 ∧ (p3 ∧ False))) ∨ (p2 ∧ p5)) ∨ p2)) ∨ (True → True)) ∨ p2) ∨ False) := by
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
theorem thm_5_vars_40202907080177703446866626625 : (((((p5 ∨ p2) ∧ (((False ∧ (p2 ∧ False)) ∨ (p5 ∨ (False ∨ ((p5 ∨ False) ∧ (((p4 ∧ p5) ∨ p4) ∧ p5))))) ∧ True)) ∧ False) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58433137779856963162463763500 : (((p2 ∨ p5) ∧ (p5 → ((True ∧ (((p2 → p4) ∧ True) → (p3 ∧ False))) → (((p2 → ((p4 ∧ p2) ∧ (p4 → p4))) → p3) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112028162693286206418135112797 : (((((p1 ∨ True) ∧ False) ∨ (p1 ∧ (((p4 ∨ (p3 → (False ∨ (True ∨ (p1 → False))))) ∨ p5) → ((p4 ∨ p3) → p5)))) ∨ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322340460931511076630149943481 : (p5 ∨ ((((False → (((p4 ∨ (p2 → True)) → (True → p5)) → ((p1 ∧ True) ∨ ((p3 → p2) → True)))) → (p1 ∧ False)) → (p4 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64707280027282755561025483219 : ((p1 ∨ (p1 → (p2 ∧ (False ∧ ((((p4 ∨ p1) → True) → p2) ∧ (True ∧ (p2 → ((False ∨ (((p4 ∨ p4) ∨ p2) ∧ p3)) ∨ p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321609781046466475439984905381 : (p4 ∨ (p3 → ((((p5 ∧ p5) ∧ (p4 ∨ (True ∨ ((p1 → p1) ∧ (p5 → p1))))) ∧ (((p5 ∨ False) → p1) ∧ (p5 ∨ p5))) → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : (p5 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : (p5 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h4.left
      let h21 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h23 : (p5 ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h24 := h20 h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h26 : (p5 ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h27 := h20 h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h4.left
      let h32 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h34 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h35 := h30 h34
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h37 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h38 := h30 h37
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157125834299662096358299795720 : ((((((p1 ∧ (p4 ∨ ((False ∧ p4) ∧ p1))) ∨ p1) ∧ ((False ∧ (p2 ∨ p2)) → True)) ∧ p2) → p5) ∨ (p3 ∨ (((p1 ∧ p3) ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300554643490876820299885167385 : (False ∨ (((p5 ∧ ((p2 ∨ (p4 ∧ (p2 ∨ True))) → p1)) → ((p5 → False) ∨ (p1 → ((p3 ∧ p3) ∨ p1)))) ∨ ((False ∧ p4) ∧ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38791179545087721479020679120 : ((((p2 ∧ ((p5 → False) ∨ True)) ∨ ((((((((False ∨ ((p4 ∧ p2) ∧ p4)) ∨ True) ∨ p4) → False) ∧ p2) ∨ p1) ∨ True) ∨ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9416722918897294589030754550 : ((((((p4 → False) ∧ p3) ∧ p4) → (p3 ∧ ((p2 ∨ ((((False ∨ p4) ∧ (p5 ∧ (False ∧ p3))) ∧ (p2 ∧ p5)) ∨ p5)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131942270716016178724237007169 : (((p5 ∨ False) ∨ (p1 ∨ (p3 ∨ ((((p3 ∨ (False ∨ (((p2 → p5) ∨ (p3 ∨ p3)) ∨ p2))) → p5) ∨ True) ∧ True)))) ∧ ((False → p2) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223764030135851288406248614467 : ((p2 ∨ (p1 → p1)) ∧ (True → (True → (((p3 ∧ p3) ∧ ((p5 ∧ (p5 ∧ p5)) → ((p2 → False) → False))) ∨ ((p1 ∧ (p3 ∧ p1)) → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49560887841821902438991600726 : ((((p1 → (((True → (((True → p4) ∨ (p2 ∧ p1)) ∨ (p1 ∨ False))) ∧ False) ∧ p3)) ∨ ((True ∧ True) ∧ p3)) → (p2 ∧ (p2 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263448983197929802661337656513 : (True ∧ (((((p3 → True) ∨ ((True → p2) ∧ (False → True))) ∧ (p5 → (p2 ∧ (((p3 ∨ p3) ∧ p4) → p4)))) → p1) → (p1 → (p1 ∧ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56435395973820296800511159967 : ((((p4 → p1) ∧ (p5 ∨ True)) → (((p3 → p1) ∧ (p4 → (p5 ∧ (p5 ∨ (((p3 ∧ p1) ∨ p4) → p1))))) ∧ (p2 ∨ (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307509640080453807914803623091 : (p1 ∨ (True → (((p3 ∧ ((p2 ∨ p3) ∨ (False ∨ False))) ∨ p1) → (p5 ∨ (p2 ∨ ((((False → p5) ∧ (True ∧ p3)) ∨ (p1 ∧ True)) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50337992417378917183074904587 : ((((((p5 ∧ (p1 ∧ True)) ∧ p1) → True) ∧ ((((True → p3) ∨ (p1 ∧ p5)) ∨ p5) → (p1 ∧ False))) ∨ ((p4 → p5) → (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149032837149951108598143186846 : (((p1 ∧ (p3 ∧ p4)) ∨ ((p4 ∧ p5) ∨ (((((False ∨ p1) ∧ p5) → (p5 → (False ∧ p3))) ∨ True) ∨ True))) ∨ (False ∧ (p4 ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_336238701360023688614869236177 : (p1 → (((p2 ∧ ((((p3 → (True ∧ p3)) ∧ (p1 → (p5 ∧ False))) ∧ p4) → (True → (p2 ∧ p5)))) ∧ (p4 ∧ ((True ∧ False) ∧ p1))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58412739968601547335592474528 : (((p2 ∨ p2) ∧ ((((((p1 → (p5 → p2)) → p2) ∧ p3) ∨ False) ∧ ((p5 ∨ (p1 → p3)) → (True → p1))) ∧ (p1 → (True → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117196494947590477195143558445 : ((True ∧ (((p1 ∧ ((p4 ∨ (p4 → p5)) → p1)) ∨ ((p4 → p5) ∧ (False ∧ p4))) ∨ ((p2 → ((p4 ∨ False) → p3)) ∧ p5))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62784086062090476656085128014 : ((p4 ∧ ((p3 → ((p5 ∨ ((p2 → p1) ∧ (p1 ∧ ((p2 ∨ (p4 ∧ True)) → (p1 ∨ p2))))) ∧ p2)) ∨ ((p2 ∧ (p4 → p4)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720696375914720994036308574087 : ((((((p4 ∨ False) → True) → True) → (p4 → ((((p3 ∧ ((p2 → True) → p3)) ∧ ((True ∨ (True → p5)) ∧ p4)) ∨ (True ∧ True)) ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178168650429062870315998401565 : ((((p4 → False) ∨ ((p2 ∧ ((False → p5) ∧ p2)) ∧ (p5 ∧ p2))) → p4) ∨ (((p3 ∨ ((p3 ∨ p5) → (p5 ∧ True))) ∧ True) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48778203161916437539429710825 : ((((p1 ∨ p2) → (((p2 ∨ (True → (p1 ∨ (p1 → (((p4 → False) → (False → p4)) ∧ False))))) → p1) ∨ p2)) ∧ (True ∨ (p3 → False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49218900433177312635878257074 : ((((True → True) ∧ ((((((False ∧ (((p1 ∨ p1) ∧ p4) ∨ p1)) ∧ True) ∨ p1) ∧ (False ∨ p4)) → False) → p1)) ∨ (False → (p1 → p1))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40477312545577832080486771619 : (((((p2 ∨ False) ∧ (((p5 ∨ p4) ∨ (p2 ∨ ((p5 → ((p2 ∧ (True ∨ (p1 → p1))) ∧ p4)) ∨ (True ∨ p4)))) → p5)) ∨ True) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328514405775548198840140796840 : (True → ((((p2 ∨ (((p5 ∨ (p2 ∧ p5)) → p1) → (p5 ∨ p4))) ∧ (True ∨ p1)) → p2) ∨ (False → (((p4 ∨ p4) → (p3 ∧ p3)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116247885925518258024799638400 : ((((p1 → p1) → False) ∨ ((p1 → p2) ∨ ((False → p3) ∧ (p5 ∧ ((True ∧ p4) → (True ∧ (p1 ∧ (False ∧ (p4 → False))))))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594151966842690249627259217711 : ((((((p3 → (False ∧ ((p5 ∧ p1) → (False ∧ p1)))) → (False ∧ ((p1 ∨ (p3 ∨ p5)) ∨ False))) → (((False → False) → p1) ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248353631589986180448892949845 : ((p2 ∨ p3) ∨ ((p2 ∧ p1) → (((p3 ∧ (p1 ∧ ((((((((p2 ∧ False) ∧ p1) → p1) ∧ p1) → False) ∧ p5) → p4) ∨ True))) → p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177918634020782029265505537151 : (((((p4 ∨ (p4 ∧ False)) ∧ (p3 ∧ p4)) ∨ ((True ∨ p1) ∧ True)) ∨ p5) ∨ ((p3 ∨ (p3 → p5)) ∨ (p3 → (True ∨ (p3 ∨ (p5 ∨ p4)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247733523284348542732633808301 : ((p1 ∨ False) ∨ ((((True → p4) ∨ (p5 ∧ p1)) ∨ (p4 ∨ ((True ∨ False) ∧ p3))) ∨ ((p2 ∨ ((True ∨ True) ∨ False)) ∨ (p2 → (False ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111860421000218987129055437373 : (((((False ∨ (((False → (p5 → p2)) → p5) ∧ (p2 ∧ True))) ∨ ((p2 ∧ p5) ∨ p3)) ∧ (((p1 → p1) ∨ p4) → p2)) ∨ p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263461250800414807262183374565 : (True ∧ (((p4 ∨ ((p1 → p3) ∨ ((((p5 → True) ∨ p1) ∧ (p2 → p1)) ∨ p1))) ∧ (((p1 ∧ p1) ∨ p1) → True)) → ((p2 ∧ False) ∨ True))) := by
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
  cases h2
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231288803493974890036265788577 : (((p5 ∨ p2) ∨ p3) → ((((p5 ∨ ((((p1 ∧ p4) ∨ True) ∨ ((((p5 ∧ p1) ∨ True) → p2) ∧ p2)) ∨ False)) → p2) ∧ (p1 → p2)) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ ((((p1 ∧ p4) ∨ True) ∨ ((((p5 ∧ p1) ∨ True) → p2) ∧ p2)) ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p5 ∨ ((((p1 ∧ p4) ∨ True) ∨ ((((p5 ∧ p1) ∨ True) → p2) ∧ p2)) ∨ False)) := by
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
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42665688627217979262067783280 : (((p4 ∨ ((p4 ∨ ((p1 ∨ p2) ∧ p5)) ∧ (p1 ∧ ((p2 ∧ (False → (p3 ∧ ((p1 → ((p2 ∧ True) ∧ True)) ∨ p1)))) ∧ p4)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136541192805428423851064147065 : ((((p2 ∧ p4) ∧ p5) ∨ ((p1 ∨ (p5 ∧ p1)) ∨ ((p3 → (((p5 → True) ∨ True) ∨ (p5 ∨ (p4 ∧ p2)))) ∧ True))) ∨ (p5 ∨ (p4 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40362630710133327067131417170 : ((((((p1 ∨ (((p1 ∨ True) ∨ p4) ∨ p2)) ∨ ((p1 ∧ ((p1 ∧ True) ∧ (p4 ∧ p3))) → ((p2 ∨ False) ∨ True))) → p2) ∨ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47032702119809029236890353104 : ((((((p4 → p1) → (((p1 ∧ (((p5 ∧ False) → p2) ∧ p1)) ∨ ((p5 ∧ p3) → True)) → p1)) ∧ p3) ∧ (p1 ∧ p1)) ∨ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311047484338870291048548923299 : (p2 ∨ ((p5 ∧ True) ∨ ((((p4 ∧ (((p3 ∨ True) ∨ (True ∨ True)) ∨ (False ∧ ((p3 → p3) ∧ (p5 → p2))))) → (p1 ∨ True)) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225378724405548880116031570964 : (((p2 ∨ p1) ∧ p2) ∨ (p5 → ((((((True → ((p5 → ((False ∨ p3) ∨ (p2 ∧ False))) ∨ p2)) → False) → p5) → False) ∨ (p3 ∧ p2)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694463732393769425903266959984 : (((((p1 ∨ p3) → (((p4 ∧ (False → p1)) ∧ p1) → ((p3 ∧ True) → p2))) ∨ (((((p4 ∨ (p4 ∨ p1)) ∨ p1) ∧ False) ∧ True) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_258788377107065255733010086633 : ((True → False) → (((((p5 ∨ p2) → p4) ∨ (p3 ∧ p3)) → p1) ∧ ((p5 → p3) → (((p5 → ((p2 → (p5 → p3)) ∧ True)) → p3) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41732393835648630997644197216 : (((((p5 ∧ p3) → (p2 ∨ p3)) ∧ (p5 → ((((p5 ∨ p1) ∨ (True ∨ (p3 ∧ p4))) → (p2 → p1)) ∨ (p3 → (p4 ∨ True))))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314452582769811086086507129493 : (p3 ∨ (((((((False ∧ (p5 ∧ (p3 ∧ p2))) → p2) ∧ (p2 ∨ p5)) ∧ (p1 ∨ False)) → (False ∧ p5)) ∨ p5) → (False ∨ (p3 → (p2 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112621813483819632250674014540 : ((((p5 ∨ (((True ∧ ((p2 → p4) ∧ ((p1 ∨ False) ∨ p1))) ∧ (p5 ∧ (p5 ∧ p5))) ∧ (p1 ∨ p1))) ∨ (True ∨ p2)) → p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215140464418278935443433153333 : (((p5 → True) → (p2 ∨ p5)) ∨ (((False ∧ p3) → ((p5 → True) ∧ p5)) ∧ ((p4 → p1) ∨ ((p3 → p5) → (p3 → (p5 ∧ (p2 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628186589532843839556498450892 : ((((((p1 ∧ True) ∧ ((p2 ∨ (((p5 → False) ∨ p4) → p5)) ∧ (p4 ∨ (((p2 → (p5 → (True ∨ p2))) → p3) → False)))) ∧ p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618582014740025579021635496038 : (((((p3 ∨ ((p1 ∧ p5) ∧ False)) → (((p3 ∧ (((p2 ∨ (p4 ∨ (p5 ∨ True))) ∧ p1) ∨ p3)) → p2) → ((p2 → p5) → p2))) ∨ p2) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∧ (((p2 ∨ (p4 ∨ (p5 ∨ True))) ∧ p1) ∨ p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40491984440883642341690184883 : (((((p2 ∨ p3) → (((p3 ∧ ((p1 ∧ (p4 ∨ (False ∨ False))) ∨ (p5 ∨ (p3 → (p4 → (p5 ∨ p5)))))) ∨ p1) ∧ p1)) ∨ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41300297987891904585471302735 : ((((p4 ∨ ((((True ∧ ((False → p3) ∨ False)) ∧ (True ∧ p1)) ∧ p2) → ((p5 ∧ p1) ∧ p4))) → (((p4 → p1) → p4) ∧ p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732462499174201159217535734710 : ((((False ∧ p4) ∧ ((False ∧ p5) ∧ (((((p1 ∧ (p2 → p2)) → p3) ∧ (p4 → (p4 → True))) ∨ p5) → ((p1 ∨ True) ∧ (True ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230562528954220187963073673654 : (((p1 → True) ∧ p2) → (((((((((p4 → p5) ∧ p5) → False) → p5) ∨ ((p4 ∨ p2) ∨ ((True → p5) ∧ p1))) ∨ False) ∨ p1) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313906220485329681803596296291 : (p3 ∨ ((p5 ∨ ((p1 ∧ ((((((p2 ∨ (p5 ∨ p4)) ∧ (p4 → True)) → False) ∧ p1) → p3) ∧ ((p4 ∨ p4) ∨ p2))) ∨ True)) ∧ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720191886312821492729363787387 : (((((p3 ∨ (p5 ∨ p1)) ∧ True) → ((((p1 ∧ (p4 ∧ p4)) ∧ (False ∨ (True ∧ (True ∨ p4)))) ∧ (p2 → p5)) → (False ∨ (p4 ∨ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65685581680791939286971897577 : ((p4 ∨ (((True ∨ True) ∧ ((p5 ∨ (p5 ∧ (False ∧ (p4 ∧ p2)))) → ((False → p1) ∨ (p2 ∨ ((p3 ∧ p1) ∧ (p1 → p2)))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303737156192286011099491707239 : (p1 ∨ (((False ∨ (p3 ∨ ((False ∨ ((p3 → (((p2 ∧ p3) ∧ p5) ∧ (True → True))) ∨ (((False → p5) ∧ False) ∧ p2))) ∨ p5))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114942428639873991978909720174 : ((((p3 ∧ (p4 → p1)) ∨ ((p1 ∨ p2) ∨ (p4 ∧ ((p4 ∧ True) → True)))) → (p1 ∧ (p2 ∧ (p2 ∧ ((p1 → True) ∨ True))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49516941979003376614178679811 : (((((p3 → (False ∧ p5)) ∧ (p3 → ((p1 ∨ ((p3 ∨ False) → ((p4 ∧ True) ∧ True))) ∧ p2))) ∧ (p3 → p3)) → ((p1 → True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303734622567515565639109864849 : (p1 ∨ (((p3 ∧ (((p5 ∧ (p5 → (((p3 ∨ (False ∨ p3)) → p1) ∨ (p3 ∧ p3)))) ∧ (True ∨ (p1 ∧ (p3 ∨ p4)))) ∧ p1)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745497736123140921783826734449 : ((((True ∨ True) → (p5 ∧ ((p3 ∧ ((p2 ∨ p5) ∧ p3)) ∨ ((False ∧ (((True → p3) ∨ (((False ∧ p5) ∧ p5) ∧ True)) → p3)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178010700869410932239124499830 : (((p5 ∨ ((p5 ∧ (p1 ∧ (((p5 ∧ True) ∨ p5) ∧ p4))) ∨ True)) ∨ p3) ∨ ((p5 → p5) ∧ (((True ∨ (p4 ∨ (p4 ∨ p1))) → p1) ∨ p3))) := by
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
theorem thm_5_vars_330600956691294741854035898687 : (True → (True → (((False ∨ ((p4 → (False ∧ False)) → p4)) ∨ ((False ∧ ((((p3 ∧ p3) ∨ (p3 → p3)) → False) ∧ p1)) ∨ (True ∨ p2))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182683199767016608675160755316 : (((p4 → ((p2 → p4) ∨ (p3 ∨ p2))) → (p2 ∨ (True ∨ True))) ∧ (((p3 ∧ p3) → True) → ((((p3 ∧ p5) → (p2 ∧ p5)) → p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71395960220147606734428879227 : ((((p4 → p1) ∧ ((p5 → ((p5 → (p3 ∨ (p3 ∧ False))) ∨ ((p2 ∨ p3) ∨ (((p4 ∨ False) ∧ True) → (p3 ∧ False))))) → p3)) ∧ p4) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761836299371664301535077061308 : (((p3 ∧ ((((((p3 ∧ p5) ∨ (((p4 ∧ p4) ∧ ((False → (p4 ∨ p3)) ∨ (False → p1))) ∨ p1)) ∨ p5) ∧ (p2 ∨ p1)) → p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346292133097261551566813426301 : (p3 → (((((p4 ∨ ((((False ∧ p2) ∨ ((True → ((p1 ∨ p5) ∨ p3)) → p4)) ∧ (False ∨ p2)) ∨ p2)) ∨ p5) ∨ p4) ∨ p1) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38192288911510461187240374433 : ((((((p3 ∧ (((p4 ∨ (p5 → ((p2 ∧ False) → p4))) ∧ True) ∧ ((p4 ∨ p3) ∨ True))) → p3) ∧ True) → (p3 ∨ (p3 → False))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68175018122273369628953092526 : ((p3 → ((((((True → (p3 ∧ True)) → ((((p5 ∧ p3) ∨ (p5 ∨ ((p4 ∧ p5) → p2))) → True) → p5)) ∨ p2) ∧ p2) ∨ p4) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43859057264176598956426832302 : (((((p5 → (((p5 ∨ True) ∧ p2) ∧ ((p4 → p4) ∨ (True ∨ p5)))) ∧ ((p3 ∨ p3) ∨ ((True ∧ p1) ∧ p5))) ∧ (p4 ∧ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



