variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135626701372735737373975233162 : ((((((p4 ∧ p4) ∨ True) → ((((p1 ∧ p5) ∨ (True ∨ p4)) ∨ p4) → p4)) ∧ True) → ((p1 ∧ p3) ∨ (p4 → p3))) ∨ (True ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260486743472471946534312169379 : ((p3 → False) → (((True → (True → (p1 → (p5 ∧ p4)))) → (True → (p2 ∧ p1))) ∨ ((p5 ∧ False) → (p4 → ((p2 → (p4 ∨ p1)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140272295047152045840827141310 : ((((p5 → ((False → (p1 → False)) → ((((False ∧ p4) ∨ p5) ∨ p3) ∧ (p2 → p4)))) → False) ∧ (p4 ∧ (p1 → p2))) → ((p3 ∧ False) ∧ p2)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p5 → ((False → (p1 → False)) → ((((False ∧ p4) ∨ p5) ∨ p3) ∧ (p2 → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h6
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h15 : (p5 → ((False → (p1 → False)) → ((((False ∧ p4) ∨ p5) ∨ p3) ∧ (p2 → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h19 := h11 h15
  -- False on the left can always be used.
  apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h24 : (p5 → ((False → (p1 → False)) → ((((False ∧ p4) ∨ p5) ∨ p3) ∧ (p2 → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h25
    -- Implications on the right can always be decomposed.
    intro h26
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h25
    -- Implications on the right can always be decomposed.
    intro h27
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h28 := h20 h24
  -- False on the left can always be used.
  apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338044977242383153066928109821 : (p1 → (((p1 → p4) ∨ (False ∧ (p1 ∧ ((p2 ∨ p3) ∨ p2)))) ∨ (p1 → (True ∧ (p4 → ((((p4 ∧ p1) ∧ p3) ∨ p4) → (p2 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327864057854990943625609585996 : (True → (((p3 ∧ p3) ∧ ((False ∧ ((True ∨ (p4 ∨ p1)) ∧ (p5 ∧ (((p3 ∧ (True → p2)) ∨ (p1 ∨ p4)) ∧ p2)))) ∨ p4)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113302388376886966040595508187 : ((((((p3 ∨ p3) ∨ (p3 ∧ p1)) ∨ p3) → (p4 ∨ ((((p2 ∧ ((True ∧ True) ∧ p2)) → p5) ∧ p4) ∧ p3))) ∧ (True ∨ False)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114969921120482809841100578178 : (((p5 → (((p2 → p2) → ((p2 → False) ∨ p3)) ∨ ((True ∨ p3) → p2))) → (p5 ∧ ((False ∧ (p4 ∧ (p2 ∧ False))) ∧ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468042900155389732589182116217 : ((((p3 ∧ (((((((p1 → p2) ∧ p2) ∧ True) ∧ p4) ∧ p5) ∧ False) ∧ p1)) ∨ (p5 ∨ ((p5 ∨ p5) → ((p4 ∧ p1) ∨ (True ∧ p5))))) ∧ True) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662768372086529357464684121267 : ((((((False → p2) → (p5 ∨ p1)) → ((((p5 → p1) → p3) ∧ (((False ∨ p2) → ((p4 ∨ p5) ∧ False)) → p3)) ∨ p2)) → (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183397958335609318732395583866 : ((False ∨ ((True → p4) → ((p3 ∨ (p2 ∨ p5)) ∨ (p1 ∨ True)))) ∧ (((False → ((((True → p2) → p2) ∨ p1) → (p3 ∧ p4))) → True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221451029528079794871250190180 : (((False → p3) ∨ True) ∧ (((((p1 → p2) ∧ p3) ∨ p2) ∨ p1) → (p3 → ((((p4 ∧ p5) → (False ∨ p2)) ∨ (p1 → (False → True))) ∨ False)))) := by
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
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48993629490206847878706452237 : ((((p4 ∧ (((False ∧ (p5 → p5)) ∨ (p2 → ((True → (p3 ∨ p1)) → (p1 ∨ (p3 → True))))) ∧ False)) ∨ p4) ∨ ((p4 → True) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159040002176600488820539754569 : ((p5 ∨ (((((False ∧ (p5 ∨ (p2 → (True ∧ ((p1 → p5) ∨ False))))) → p5) ∧ p4) ∨ True) ∧ False)) ∨ ((p3 ∧ p1) ∨ (False → (p1 → p1)))) := by
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
theorem thm_5_vars_672336275887230100656698669369 : ((((((True ∨ (p3 ∨ ((p4 → p1) → ((True → True) ∧ (((p1 ∨ p5) ∧ p3) ∧ False))))) → (p5 ∧ p5)) → p4) → ((True → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667026339067965643619883937816 : ((((((p2 ∧ True) ∨ (p2 ∨ p2)) → ((((p3 → ((p4 → False) ∨ p2)) → True) → (False ∧ p4)) ∧ (p2 ∧ p1))) ∧ ((p4 → p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169010400980215460692323661756 : ((p1 → ((False → p4) → (p2 → ((((p2 → p5) ∧ (True ∧ True)) ∨ (p3 ∨ False)) ∨ True)))) → ((p5 ∧ (((p3 ∧ p3) ∧ p1) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249139661120374140258201633021 : ((p4 ∨ p2) ∨ ((p3 → (p2 ∧ p4)) → (((p2 ∨ (p1 → ((p2 ∧ (p3 ∨ (p5 ∧ (p5 ∧ False)))) ∧ (False ∨ (True → p4))))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306607225728582578673845505983 : (p1 ∨ ((p2 → p2) → ((False → p3) ∧ (((p4 ∨ (p1 ∨ (False ∧ (((p4 ∨ (p1 ∨ False)) → True) ∧ p3)))) ∧ (True → False)) → (p1 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117485316638477104137840844762 : ((p1 ∧ (p5 ∨ ((((((p5 ∧ (True → p1)) → p3) ∨ p4) ∨ (((p3 → (p1 → p5)) → False) → p5)) ∧ (True ∧ p5)) → False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198388973386650169544307892796 : ((p3 ∧ (False ∧ ((p1 ∨ (p1 → p4)) ∧ False))) ∨ ((False ∨ True) ∧ (((p4 ∨ (False → True)) ∨ p2) ∨ ((True ∧ (p5 ∨ (p3 ∨ p4))) → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164375240858468308732058264188 : ((p3 → (p5 → ((((((p4 → p4) → False) → (p1 → (p1 ∨ p4))) → False) ∨ p1) ∨ p5))) ∧ (((True ∨ False) → p4) ∨ (True ∧ (False → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310025007524444360084968870972 : (p2 ∨ ((((p2 ∨ p2) → ((False ∨ p5) → ((p5 → (p1 ∧ p2)) ∨ p3))) ∧ (p4 → p2)) ∨ ((True ∨ p2) → (p3 ∨ ((False → True) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227037661644572976212886602898 : (((p2 ∨ p2) → p3) ∨ ((((p5 ∧ (False → (p1 ∧ ((False ∧ (p2 ∨ False)) ∨ p1)))) → (p5 → p3)) → ((p4 ∧ p4) ∨ (p1 ∨ True))) ∨ p4)) := by
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
theorem thm_5_vars_256941935194288942327277347499 : ((p1 ∨ p5) → ((((True ∧ (((p1 ∨ True) ∧ True) → ((((p2 ∨ True) → (p4 → (p3 → p2))) → p5) ∨ p2))) ∨ False) ∧ (p4 → p2)) ∨ True)) := by
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
theorem thm_5_vars_48464636449043454128261164098 : (((((p5 ∧ (p3 → (p1 ∧ (p4 ∨ (True ∨ ((p5 → (((p2 → p5) → p1) ∧ False)) → p1)))))) → p2) ∧ p5) ∧ ((True ∧ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762308560153357716425246840604 : (((p3 ∧ ((((p1 ∨ p1) ∨ (True ∨ p2)) ∧ (p5 → ((p5 → (p4 ∨ (False ∧ ((p3 ∨ p4) → p4)))) → p3))) ∧ ((p4 → p5) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723903057163416302691480986598 : ((((True ∧ (p2 ∨ p3)) ∧ ((p5 → ((((False ∧ p4) ∨ (p4 ∧ p4)) ∨ ((p3 → (False ∧ (p3 ∧ (p1 → p2)))) ∨ p2)) ∨ p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249979196309010500752150654252 : ((True → p2) ∨ (((p3 → ((p2 ∨ (p1 ∨ False)) ∨ p5)) → ((False → (False ∧ p4)) → False)) ∨ ((True ∨ (p4 ∨ (p1 ∨ (p1 → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118829834909970930778285414760 : ((True → (((p3 ∨ (False ∨ ((p3 → ((p4 ∨ ((p2 ∨ p2) → (True ∨ True))) → p2)) ∧ (True ∨ p1)))) ∧ p5) ∧ (False → p3))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150013049427032007761479394616 : ((p5 ∨ (((p3 ∨ p5) → (p5 ∨ ((False ∧ (True → ((p1 ∧ (True → p5)) ∧ p2))) ∧ p1))) ∧ (p2 → p4))) ∨ ((p4 ∧ (p3 ∧ p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159745349737010563400175054641 : (((((p4 ∧ p1) ∨ (False ∧ p4)) ∨ ((p1 ∨ (p1 ∨ (p2 ∨ p3))) ∧ (False ∨ (p3 → p3)))) ∨ p5) → ((True ∧ ((p2 ∨ True) ∨ p5)) ∨ p5)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h18 =>
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
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
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h22 =>
              -- False on the left can always be used.
              apply False.elim h22
            case inr h23 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h25 =>
              -- False on the left can always be used.
              apply False.elim h25
            case inr h26 =>
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
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42415630074605205076163748782 : (((p5 ∧ ((((p2 ∨ (p2 ∧ (p5 → ((p2 → p5) ∨ (p4 ∧ p5))))) ∧ (p5 ∧ (p1 → (p2 ∧ p1)))) → (p1 ∨ p3)) → p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118598982091438607033491636559 : ((p4 ∨ ((p4 ∧ (((p3 → p2) ∧ p1) → ((True → ((True ∧ ((p4 ∧ p2) → (p3 → p2))) ∨ p2)) ∧ p4))) ∨ (p4 → p4))) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223834287261600742135421266925 : ((p3 ∨ (True ∨ p5)) ∧ ((((p4 ∨ ((((p3 → p5) ∨ p2) ∨ (p1 ∧ p2)) ∧ p2)) → (p3 ∨ p5)) ∨ (False → p2)) ∨ (p2 → (p5 ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693819726227347611192089783519 : ((((((((p2 ∧ p2) → (p3 ∧ p5)) ∨ p4) → ((p3 ∨ p1) ∧ p1)) → p4) ∨ ((False → False) → ((p1 ∨ ((p3 ∧ p2) ∧ p1)) → p1))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344471396656198566341042732878 : (p2 → (True → ((p3 ∧ ((p5 → p5) → ((p1 → p3) → (p3 ∧ ((p2 → (False ∧ (False ∧ p2))) → (((p3 ∨ True) ∨ False) ∨ p2)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136165383094131070690320257151 : (((p1 → ((p4 ∧ True) ∨ ((p2 → p4) → p1))) → ((True → False) → (p4 ∧ (False ∨ ((p1 ∧ p5) → (p5 ∧ p2)))))) ∨ (False ∧ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179705494942518567203127477757 : (((((False ∧ p2) ∧ (((True ∨ True) → p1) → (p3 ∧ False))) ∨ p5) ∧ p1) → ((p1 → False) ∨ ((p5 → p4) ∨ ((True ∧ True) ∧ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150897114218400380492981118279 : (((((False → p4) ∨ False) ∨ (p5 → (p2 ∨ (((p5 ∨ p4) → True) ∨ (((p3 ∨ p4) → p4) ∧ p5))))) ∨ p3) → ((True → (p2 ∧ p3)) → p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h6 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h7 := h2 h6
        -- We need to get the right conjuct of h7 based on <expert-advice>.
        let h8 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209033083366094713934520193721 : ((False ∨ (p3 → (False ∧ (p4 ∨ True)))) → ((((p5 ∨ (False ∨ p3)) ∧ False) ∧ p3) ∨ ((p1 ∧ p5) → ((p3 → p5) ∨ (True ∨ (p5 ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
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
theorem thm_5_vars_646265427771705146460004818967 : ((((False → ((p2 ∨ ((p4 ∨ ((p4 → p3) → p1)) ∨ p2)) ∧ ((True ∨ (((p2 → p3) ∨ (p5 ∧ (False ∨ p5))) ∧ False)) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249691373328537676305197765728 : ((p5 ∨ p4) ∨ (True ∧ (((((p4 ∨ p1) ∧ (p5 ∨ False)) ∨ p4) → ((False ∧ p2) ∨ (True ∨ p3))) ∨ ((p1 ∨ p2) ∨ (p3 → (p3 → p5)))))) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810377833041117159531470476152 : (((p5 → (((((p3 ∧ p3) ∨ p1) ∧ p3) ∨ (p2 → (p3 ∧ True))) → (((p2 ∧ ((p2 → p1) → False)) ∧ (p5 → (p4 ∨ False))) ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173677371584689913051993836606 : ((((((p1 → p5) → p5) ∨ (p2 → ((p5 ∧ p1) ∧ (p1 → p5)))) ∨ p1) ∨ p3) → (((True ∧ True) → p4) ∨ ((False ∧ False) → (True → False)))) := by
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
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h5.left
        let h8 := h5.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348233069770217936594294723905 : (p3 → ((p5 → p4) → (((p2 ∨ True) ∧ (p3 ∨ p3)) → (((p4 ∧ (p3 ∧ p1)) → ((True → p3) ∧ p5)) → (True ∧ ((p4 ∧ p2) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786431045122938333790407221297 : (((p4 ∨ ((False ∨ (((((False ∨ p5) → False) ∧ False) ∧ p5) ∧ ((True → p4) → p5))) ∨ (True → ((True → False) ∨ (False → (False ∨ False)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762882340512526152320867115406 : (((p3 ∧ (((p4 ∧ p5) ∧ ((p3 ∨ p4) ∨ p5)) ∨ (p2 ∨ (((p5 ∨ p1) ∨ ((((p2 → p1) ∧ p2) ∧ (p5 → p2)) ∨ False)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65206055301510859753160081859 : ((p3 ∨ (((p2 ∨ (p1 ∨ (((p1 ∧ (p5 ∨ ((False → (p5 ∨ p4)) ∧ ((p4 ∨ (False → p4)) ∧ p4)))) ∧ p5) → p1))) → p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55837146476045234052028481198 : (((False ∧ (False ∨ (p1 ∧ p1))) ∧ (p5 ∨ (True → ((True ∧ p3) ∨ ((p1 ∨ p4) ∨ ((((p5 ∨ (p5 → p1)) ∧ p4) → False) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134364561094854438490657384396 : (((p1 ∨ ((((p2 ∧ False) → True) ∧ p2) → ((False ∨ ((p4 ∧ True) ∨ ((p1 ∨ (p5 ∨ p5)) ∨ p1))) ∨ p3))) ∨ True) ∨ ((p1 → p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698100310239410031068871108010 : (((((p1 ∨ (((p4 ∧ True) ∧ (p5 → (p4 ∧ True))) ∧ True)) ∨ p5) ∨ (((True ∨ False) → (((True → False) → p1) ∨ p2)) ∨ (p1 ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666194491863044461454610310250 : ((((((False ∧ p3) ∨ ((((p2 ∨ False) → (p3 ∨ (((p5 ∧ p3) ∧ p1) ∧ False))) ∧ p5) ∨ True)) ∨ (False → False)) ∧ (True ∧ (False → p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599407556646372318813736763793 : (((((p5 ∧ False) ∨ ((p3 ∨ (((p2 ∨ p1) → (((True ∧ p4) → (p4 ∨ (p3 ∧ p4))) ∧ ((True ∨ p3) ∨ p4))) ∧ p4)) ∨ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86749059925487545770629061734 : (((p5 → ((p3 ∧ (False ∧ (p2 ∧ True))) ∧ p1)) ∧ (((p5 ∨ (p5 ∨ p5)) ∧ (p5 ∧ True)) ∧ (((p2 ∨ p3) ∨ p5) ∨ (p3 ∨ p2)))) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- We need to get the right conjuct of h16 based on <expert-advice>.
          let h17 := h16.right
          -- We need to get the left conjuct of h17 based on <expert-advice>.
          let h18 := h17.left
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h20 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h21 := h2 h20
          -- We need to get the left conjuct of h21 based on <expert-advice>.
          let h22 := h21.left
          -- We need to get the right conjuct of h22 based on <expert-advice>.
          let h23 := h22.right
          -- We need to get the left conjuct of h23 based on <expert-advice>.
          let h24 := h23.left
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h26
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h33 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h34 := h2 h33
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- We need to get the right conjuct of h35 based on <expert-advice>.
        let h36 := h35.right
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h39
        -- We need to get the left conjuct of h40 based on <expert-advice>.
        let h41 := h40.left
        -- We need to get the right conjuct of h41 based on <expert-advice>.
        let h42 := h41.right
        -- We need to get the left conjuct of h42 based on <expert-advice>.
        let h43 := h42.left
        -- False on the left can always be used.
        apply False.elim h43
  case inr h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h7.left
      let h47 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h49 =>
          -- Disjunctions on the left can always be decomposed.
          cases h49
          case inl h50 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h51 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h46
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h52 := h2 h51
            -- We need to get the left conjuct of h52 based on <expert-advice>.
            let h53 := h52.left
            -- We need to get the right conjuct of h53 based on <expert-advice>.
            let h54 := h53.right
            -- We need to get the left conjuct of h54 based on <expert-advice>.
            let h55 := h54.left
            -- False on the left can always be used.
            apply False.elim h55
          case inr h56 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h57 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h46
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h58 := h2 h57
            -- We need to get the left conjuct of h58 based on <expert-advice>.
            let h59 := h58.left
            -- We need to get the right conjuct of h59 based on <expert-advice>.
            let h60 := h59.right
            -- We need to get the left conjuct of h60 based on <expert-advice>.
            let h61 := h60.left
            -- False on the left can always be used.
            apply False.elim h61
        case inr h62 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h63 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h62
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h64 := h2 h63
          -- We need to get the left conjuct of h64 based on <expert-advice>.
          let h65 := h64.left
          -- We need to get the right conjuct of h65 based on <expert-advice>.
          let h66 := h65.right
          -- We need to get the left conjuct of h66 based on <expert-advice>.
          let h67 := h66.left
          -- False on the left can always be used.
          apply False.elim h67
      case inr h68 =>
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h69 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h70 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h46
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h71 := h2 h70
          -- We need to get the left conjuct of h71 based on <expert-advice>.
          let h72 := h71.left
          -- We need to get the right conjuct of h72 based on <expert-advice>.
          let h73 := h72.right
          -- We need to get the left conjuct of h73 based on <expert-advice>.
          let h74 := h73.left
          -- False on the left can always be used.
          apply False.elim h74
        case inr h75 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h76 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h46
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h77 := h2 h76
          -- We need to get the left conjuct of h77 based on <expert-advice>.
          let h78 := h77.left
          -- We need to get the right conjuct of h78 based on <expert-advice>.
          let h79 := h78.right
          -- We need to get the left conjuct of h79 based on <expert-advice>.
          let h80 := h79.left
          -- False on the left can always be used.
          apply False.elim h80
    case inr h81 =>
      -- Conjunctions on the left can always be decomposed.
      let h82 := h7.left
      let h83 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h84 =>
        -- Disjunctions on the left can always be decomposed.
        cases h84
        case inl h85 =>
          -- Disjunctions on the left can always be decomposed.
          cases h85
          case inl h86 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h87 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h82
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h88 := h2 h87
            -- We need to get the left conjuct of h88 based on <expert-advice>.
            let h89 := h88.left
            -- We need to get the right conjuct of h89 based on <expert-advice>.
            let h90 := h89.right
            -- We need to get the left conjuct of h90 based on <expert-advice>.
            let h91 := h90.left
            -- False on the left can always be used.
            apply False.elim h91
          case inr h92 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h93 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h82
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h94 := h2 h93
            -- We need to get the left conjuct of h94 based on <expert-advice>.
            let h95 := h94.left
            -- We need to get the right conjuct of h95 based on <expert-advice>.
            let h96 := h95.right
            -- We need to get the left conjuct of h96 based on <expert-advice>.
            let h97 := h96.left
            -- False on the left can always be used.
            apply False.elim h97
        case inr h98 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h99 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h98
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h100 := h2 h99
          -- We need to get the left conjuct of h100 based on <expert-advice>.
          let h101 := h100.left
          -- We need to get the right conjuct of h101 based on <expert-advice>.
          let h102 := h101.right
          -- We need to get the left conjuct of h102 based on <expert-advice>.
          let h103 := h102.left
          -- False on the left can always be used.
          apply False.elim h103
      case inr h104 =>
        -- Disjunctions on the left can always be decomposed.
        cases h104
        case inl h105 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h106 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h82
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h107 := h2 h106
          -- We need to get the left conjuct of h107 based on <expert-advice>.
          let h108 := h107.left
          -- We need to get the right conjuct of h108 based on <expert-advice>.
          let h109 := h108.right
          -- We need to get the left conjuct of h109 based on <expert-advice>.
          let h110 := h109.left
          -- False on the left can always be used.
          apply False.elim h110
        case inr h111 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h112 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h82
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h113 := h2 h112
          -- We need to get the left conjuct of h113 based on <expert-advice>.
          let h114 := h113.left
          -- We need to get the right conjuct of h114 based on <expert-advice>.
          let h115 := h114.right
          -- We need to get the left conjuct of h115 based on <expert-advice>.
          let h116 := h115.left
          -- False on the left can always be used.
          apply False.elim h116



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112421906125643232076875052857 : ((((p1 → (p3 ∨ ((((p3 ∨ p5) → p1) → (True → p3)) → ((((p3 ∧ p1) ∧ p5) ∨ (p2 ∧ p4)) ∨ p4)))) ∧ p2) → p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230210856583917260744383812485 : (((True ∨ True) ∧ p5) → (((p5 → ((True → ((False → p4) ∧ p5)) ∧ False)) → ((((p1 ∧ p4) ∨ p1) → (p2 ∧ p1)) → p4)) ∨ (True ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625696266214923279734770330443 : ((((p1 → (((((p4 → p2) ∨ p5) ∨ ((p3 → (False ∨ p2)) ∧ p3)) → p5) ∧ ((p5 ∧ ((p3 ∧ p1) ∨ False)) → (p1 ∨ p2)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105775561170708971568618801552 : ((((((p4 ∧ (p1 ∨ p3)) ∨ ((p1 → (True ∧ p1)) ∨ (p4 ∨ False))) ∨ False) ∨ p4) → (False ∨ (p2 → (p2 ∨ (p2 ∨ False))))) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Implications on the right can always be decomposed.
  intro h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56279141399987426003948133936 : (((p5 → ((p3 → p1) ∧ p3)) ∨ ((p1 → ((p2 ∧ (((p5 ∧ False) ∧ (True ∧ p2)) ∨ p3)) → ((True → False) ∨ p1))) → (p1 → p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221571335348629683877267890640 : (((p3 → p3) ∨ p2) ∧ (((((((p1 ∧ p1) ∨ p5) ∧ p3) ∧ p2) ∧ p1) ∧ (((p1 ∧ (p3 ∧ (p4 → p4))) ∧ p5) → False)) ∨ (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244637596224082742935542049779 : ((False ∧ p5) ∨ ((((p4 ∨ p3) ∧ p3) ∧ (True → ((True ∨ p5) → p3))) ∨ (((((p4 ∧ False) ∨ True) ∧ (False ∧ False)) → (False ∨ True)) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620175213607497089329597820479 : (((((p2 ∧ p4) ∨ ((((True → ((((p4 ∨ p3) ∧ False) ∨ ((p5 → True) ∨ p5)) ∨ p3)) ∨ p1) ∧ (True ∨ (p5 → p2))) ∨ p4)) ∨ p5) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312100670335979312044929646331 : (p2 ∨ (True → ((((((((p4 ∧ ((p4 ∧ (p5 ∧ ((p2 → True) → p5))) ∨ p5)) ∨ False) ∨ p2) ∧ (p5 → True)) ∨ p1) → p2) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_140301638778653315517575438095 : ((((p5 → p2) ∨ (((p1 → p2) ∨ p3) ∧ (((((False → p1) ∨ p1) ∨ p5) ∨ p2) ∨ p4))) ∧ (False → (True ∨ True))) → ((p1 ∧ p3) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
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
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327019549163293019472660669231 : (True → (((p1 → ((p2 ∧ (((p1 ∧ p4) ∧ p4) ∧ (p2 → (p4 ∨ p2)))) ∨ p5)) ∨ (p2 ∨ (((p4 → p4) → p5) ∧ (True ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803304653135127411063244698753 : (((p3 → ((((p5 ∨ (False ∨ True)) ∨ (p3 ∨ (p1 ∨ True))) ∧ (p2 ∨ (p5 ∨ (((False ∧ p5) ∨ ((p4 → True) → p4)) ∨ False)))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_53796596979700679255322523674 : (((((p3 → (p2 ∧ (False ∨ p5))) ∧ (p1 → False)) → p4) ∨ ((p2 ∨ ((((False ∧ (True ∧ p1)) ∧ p2) ∧ p3) ∧ (False ∨ p3))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185428225969433247310071917261 : ((False ∨ ((p2 ∨ ((False → (False ∧ p5)) → (p3 ∨ p1))) ∧ p5)) ∨ (False → (((p5 ∨ p5) ∨ (p5 ∨ ((True ∨ p2) ∨ (p2 ∧ p2)))) ∧ p3))) := by
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
theorem thm_5_vars_159072266742049547043797993075 : ((p5 ∨ (p3 ∨ (p4 ∧ (((False ∨ (p4 ∧ p1)) ∨ p3) ∨ ((p5 ∧ (p3 ∨ p3)) → (False → p4)))))) ∨ ((p5 ∨ ((False ∧ p3) → True)) ∨ p1)) := by
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
theorem thm_5_vars_624030541361046118747877950220 : ((((p2 ∨ ((((p1 → (False → (p4 ∧ p3))) ∧ p1) ∨ (((p1 ∧ p1) → True) → (p5 ∧ p2))) ∨ ((p4 ∨ (True ∧ p3)) ∨ p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_752622939916311347789454583391 : (((False ∧ (((p3 ∨ (p5 ∧ (((p4 ∧ ((((True ∧ (True ∧ p2)) ∨ False) → ((False → p3) → p3)) ∨ p5)) ∧ p5) ∨ p5))) ∨ p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54729799770905672170393341209 : (((((p5 ∧ True) ∨ p2) ∨ ((p2 → p4) ∧ p2)) → (((p5 ∧ ((p5 → (p1 ∧ p1)) ∧ (True ∨ p5))) ∨ ((p5 → p2) ∧ False)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221405999295520724379089370128 : (((True → p2) ∨ True) ∧ (((p3 ∨ ((p5 ∧ (p2 ∧ p3)) ∧ p5)) ∧ (p3 ∨ False)) ∨ (p3 ∨ ((p4 ∨ (p3 ∨ True)) ∨ ((p3 ∧ p2) ∧ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62658617956473360344622041250 : ((p4 ∧ ((((True ∧ (p5 ∧ True)) ∨ ((((True ∧ p4) ∧ p5) → p5) ∧ (p5 ∨ (True ∨ (True ∧ (p3 ∨ p5)))))) → (p2 ∧ p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174122055255887544633038790922 : (((True → (p2 → ((p1 → ((False ∧ p3) ∧ (p5 ∧ p2))) → True))) ∧ (p3 → False)) → ((p5 ∨ (p1 ∨ (((p3 → p1) ∧ p5) → p3))) ∨ True)) := by
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
theorem thm_5_vars_192456247655169717361841495807 : (((((p4 → p4) → (True → False)) ∧ (p5 → True)) ∨ False) → (((p5 ∨ ((p4 ∨ p5) ∧ (p4 ∨ (p2 ∧ p5)))) ∧ (p1 ∨ (p5 ∧ False))) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : (p4 → p4) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h10
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h25.left
            let h27 := h25.right
            -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
            have h28 : (p4 → p4) := by
              -- Implications on the right can always be decomposed.
              intro h29
              -- One of the premise coincides with the conclusion.
              exact h29
            -- We have shown the premise of h26, we can now drive its conclusion.
            let h30 := h26 h28
            -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
            have h31 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h30, we can now drive its conclusion.
            let h32 := h30 h31
            -- False on the left can always be used.
            apply False.elim h32
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- False on the left can always be used.
          apply False.elim h36
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- One of the premise coincides with the conclusion.
            exact h38
          case inr h44 =>
            -- False on the left can always be used.
            apply False.elim h44
        case inr h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- False on the left can always be used.
          apply False.elim h47
    case inr h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h51 =>
            -- Conjunctions on the left can always be decomposed.
            let h52 := h51.left
            let h53 := h51.right
            -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
            have h54 : (p4 → p4) := by
              -- Implications on the right can always be decomposed.
              intro h55
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h52, we can now drive its conclusion.
            let h56 := h52 h54
            -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
            have h57 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h56, we can now drive its conclusion.
            let h58 := h56 h57
            -- False on the left can always be used.
            apply False.elim h58
          case inr h59 =>
            -- False on the left can always be used.
            apply False.elim h59
        case inr h60 =>
          -- Conjunctions on the left can always be decomposed.
          let h61 := h60.left
          let h62 := h60.right
          -- False on the left can always be used.
          apply False.elim h62
      case inr h63 =>
        -- Conjunctions on the left can always be decomposed.
        let h64 := h63.left
        let h65 := h63.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h66 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h67 =>
            -- Conjunctions on the left can always be decomposed.
            let h68 := h67.left
            let h69 := h67.right
            -- One of the premise coincides with the conclusion.
            exact h64
          case inr h70 =>
            -- False on the left can always be used.
            apply False.elim h70
        case inr h71 =>
          -- Conjunctions on the left can always be decomposed.
          let h72 := h71.left
          let h73 := h71.right
          -- False on the left can always be used.
          apply False.elim h73



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112937530358156309533909457402 : ((((True → p3) → ((True ∧ ((p4 → p5) ∨ ((p3 ∧ (p3 ∨ ((p5 ∧ (p4 → (False ∧ p2))) → False))) ∨ True))) ∧ False)) → p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263843051008884495472117752359 : (True ∧ ((True ∨ ((((p5 → (p5 ∧ p3)) ∨ (p3 ∧ False)) ∧ (p4 ∨ p3)) ∨ (p3 ∨ p4))) → ((p1 ∨ (True ∨ ((p2 → p3) → p4))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137776662276876719417270109125 : ((p2 ∨ ((((False → False) → p4) ∧ (p4 ∧ (p4 ∨ p2))) → (True → ((False ∧ (p4 → ((p3 → p4) ∧ True))) ∨ p3)))) ∨ (p5 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342387344991169167484338215049 : (p2 → (((p1 ∧ ((p1 ∧ p4) ∨ ((p4 ∨ (p2 ∧ (p2 ∨ p3))) ∨ False))) ∨ (p5 ∨ p1)) ∨ ((p1 ∧ p1) ∨ (False ∨ (True ∧ (False ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315823021069549043185831807925 : (p3 ∨ ((p4 ∨ True) → (p1 → ((p5 ∧ False) ∨ (((p1 → p5) → p1) ∧ (((False → p4) → ((True → ((p1 ∨ p1) ∧ p5)) ∧ p2)) ∨ p1)))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158779389001937763937847746756 : ((p5 ∧ (((((p3 → (p3 ∧ (p5 ∧ (p2 ∧ p3)))) ∧ p3) ∨ p1) ∧ (p1 → (p5 ∧ p4))) ∧ p2)) ∨ ((True → (p3 → (p4 → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148294069122498179115246692243 : ((((p1 → ((p1 ∧ (p3 → ((True ∧ p3) ∧ p5))) → p3)) → (p2 → (p3 ∧ p4))) → ((p1 → p3) → p4)) ∨ ((False → p5) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226562886498709031825171321207 : (((p4 → p2) ∨ False) ∨ ((((((True ∧ (p3 ∧ p4)) ∨ ((p4 ∧ (p1 → p5)) → p4)) ∨ ((p1 ∨ p2) ∧ p3)) → (False ∧ True)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55778309270312948393251313934 : ((((p1 → p2) ∧ (False ∨ p5)) ∧ ((p4 ∨ ((p1 ∧ (p2 ∨ (p5 ∨ (((p3 ∧ True) → (p3 → True)) ∨ True)))) ∧ p4)) ∧ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197473003691635123846313755598 : ((((p4 → p2) ∧ (False → p3)) ∧ (p5 → p2)) ∨ ((((p1 ∨ (p5 ∧ ((p1 ∨ p2) → p4))) ∨ p5) → (p4 ∨ ((p5 ∧ True) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337375727259842690139208725318 : (p1 → (((p3 ∧ (p3 ∨ True)) ∧ ((((((True ∨ p1) ∧ ((True ∧ (False → p3)) ∨ p4)) ∨ True) ∨ p1) ∨ p1) → False)) ∨ (p3 → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647775047162562925513131445697 : ((((p5 → (p5 → (p5 ∧ (((True ∨ False) → (((p5 ∧ (p1 ∨ (((True ∧ p5) ∧ True) → (p1 → True)))) ∨ p1) → True)) ∨ False)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136326006740010935114074826221 : ((((True → p3) ∧ (p1 ∧ True)) ∧ ((False ∨ ((p1 ∨ False) ∨ (False → True))) → (p2 → ((p1 ∧ False) ∧ (p3 ∧ p1))))) ∨ ((p1 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_859917044427351170440399573865 : (((((((p1 → (False ∧ (((p1 → p4) → ((p2 ∨ ((p1 ∧ False) → (p3 ∨ p3))) ∨ p5)) ∧ p2))) → p4) → p2) ∨ (False → p1)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → (False ∧ (((p1 → p4) → ((p2 ∨ ((p1 ∧ False) → (p3 ∨ p3))) ∨ p5)) ∧ p2))) → p4) → p2) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116732928685761880333629408068 : (((p3 ∧ p4) ∨ (((p4 ∨ (p2 → (p4 ∧ (p3 → p5)))) ∧ (((p4 ∧ ((p4 ∧ p1) ∧ p5)) ∨ p5) ∨ p1)) → (p4 ∨ p2))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166077915254724495529422653558 : (((p1 ∨ p4) → (((p5 ∨ (p5 ∧ p5)) ∧ (p2 ∨ (p5 ∧ (p4 → p5)))) → (True → False))) ∨ (True ∨ (True ∧ ((p3 ∨ (p2 → True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734620485014020251597130786683 : ((((p1 ∨ p3) ∧ (((p4 ∧ (p2 → (p2 ∧ (False ∨ True)))) ∨ (False → (p2 → p1))) ∧ (((p5 ∧ p3) ∧ True) → (p1 → (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89359467921279789105607123353 : (((True → (False ∧ p3)) ∧ (p3 ∧ (p3 ∨ (((((p5 ∧ ((p1 ∧ True) → p5)) ∧ (p2 ∨ False)) ∨ False) ∨ (p4 ∨ False)) ∨ (False → p4))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h14.left
          let h17 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h18 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h23
          -- We need to get the left conjuct of h24 based on <expert-advice>.
          let h25 := h24.left
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h29 := h2 h28
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260602379486541333147902679409 : ((p3 → p2) → ((((p5 ∧ True) ∧ (p3 ∨ p2)) → (((((False → (p4 ∨ p1)) ∧ (True ∧ p3)) ∨ p5) → False) → p2)) → (p2 ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305600836177095430215141378731 : (p1 ∨ ((p2 ∨ (False ∨ (((p5 ∧ p1) ∧ (False ∧ p3)) ∨ (p4 ∧ p1)))) ∨ ((p4 → (p1 ∨ False)) → (((p4 ∧ (True ∧ p1)) → True) ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51801382121922997733731021271 : (((p2 ∨ (((p1 ∧ p3) ∨ ((p5 ∧ p2) → True)) ∧ (p2 ∨ (p3 ∧ (p3 ∧ p4))))) ∧ ((p5 ∨ ((True ∨ True) ∧ p1)) ∨ (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159246793831445726404628781655 : ((p3 → (((p1 ∨ True) → (p1 ∧ p3)) ∧ (p1 ∨ ((((p4 ∧ p4) ∨ p5) ∧ p2) ∨ (p4 ∧ p4))))) ∨ ((True → (p4 ∧ (p1 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703127842184919598530366421929 : (((((p2 ∧ True) → ((False ∧ ((False ∧ p5) ∨ p3)) ∨ p1)) ∨ ((p1 → ((p5 ∧ p4) ∧ p2)) → (((p3 ∧ p3) ∨ p3) → (p2 ∨ p3)))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785630619346858920030920287918 : (((p4 ∨ (((False ∨ (((((p2 → p2) → p3) → ((p3 ∧ True) ∨ p3)) ∧ p4) ∨ (((True → p3) ∧ p3) ∧ (True ∧ True)))) ∨ p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



