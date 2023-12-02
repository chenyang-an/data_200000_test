variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51187919624412170749672128043 : (((((((((p4 ∧ True) ∧ True) ∨ (p3 → p4)) ∧ p4) → False) → p5) ∨ ((p1 → p2) ∨ p1)) ∨ (((True → False) → (p4 ∨ False)) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300098832413708628426004446729 : (False ∨ ((((((True ∨ p4) ∨ (p4 ∨ (((p5 ∧ True) ∨ p1) ∨ True))) ∧ p2) ∧ (p2 ∨ p5)) ∨ ((p5 ∨ (p2 → p3)) ∨ p4)) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137070517380402196470981206623 : (((p4 → p1) → ((False → (False ∨ ((p2 ∧ ((((p5 → p3) ∧ (False → False)) ∨ p4) → p4)) ∧ p5))) → (True ∧ p1))) ∨ ((False → p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319589080488677753309513226631 : (p4 ∨ ((p3 ∨ ((((False ∨ p1) → (p4 → False)) → True) ∧ p3)) → ((((p3 ∧ False) ∧ ((p1 ∧ p2) ∨ p5)) ∧ p2) ∨ (p3 ∧ (True ∨ p4))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205641626890932513446946314351 : (((p4 ∧ p4) ∨ ((False ∨ p3) ∧ p1)) ∨ ((((p3 → p4) → (p5 → p5)) ∨ (((False ∧ (((p4 ∧ False) ∨ p4) → p5)) ∨ True) → p4)) ∨ p5)) := by
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
theorem thm_5_vars_46980106902570828409181075000 : ((((((((False → p5) ∨ (((True ∧ p3) ∧ True) → (p1 → (p5 → p1)))) ∨ (p4 ∧ p3)) ∧ p3) → (p2 → p2)) → False) ∨ (p2 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227888591060663510861431212351 : ((p2 ∧ (True → p5)) ∨ (((p1 ∨ p3) → (p1 ∨ (((((p4 ∧ (p1 ∧ p3)) ∨ False) → False) ∨ p2) ∧ p1))) ∨ ((p2 ∨ p1) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_179132506150715870271776570842 : ((p1 ∧ ((p4 ∨ (True ∧ False)) ∧ (True ∨ (p1 ∧ ((p4 ∧ p3) → False))))) ∨ (True ∧ (((((p1 → p3) ∨ p2) ∨ (p2 → p5)) ∨ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633114395092477002110063418131 : ((((((True → False) → ((((((p4 ∨ (p4 → p3)) ∨ p5) → p3) ∧ False) → (p1 ∧ (p1 ∨ True))) ∧ (True ∨ p5))) ∧ (p3 ∧ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41105505796996931285033373613 : (((((True ∧ (p5 ∨ p1)) ∧ ((p2 ∨ ((True → p4) → ((p3 ∨ p5) ∨ ((p4 ∨ True) ∧ p5)))) ∨ p3)) ∧ (p1 → (p4 → p5))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140294689583452113613112236628 : ((((True → (False ∧ p1)) ∧ (((p2 ∧ True) ∧ p5) ∨ ((True ∧ p1) ∧ ((True → p5) ∨ p4)))) ∧ (p3 → (p3 ∧ False))) → ((True ∧ p3) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h25 := h4 h24
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- False on the left can always be used.
      apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- One of the premise coincides with the conclusion.
    exact h33
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h41 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h43 := h29 h42
      -- We need to get the left conjuct of h43 based on <expert-advice>.
      let h44 := h43.left
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h46 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h47 := h29 h46
      -- We need to get the left conjuct of h47 based on <expert-advice>.
      let h48 := h47.left
      -- False on the left can always be used.
      apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246508443838869627379203485622 : ((p5 ∧ p1) ∨ ((((p3 → (p2 → (False ∧ p3))) ∧ (p2 → True)) ∧ (p4 ∧ ((False ∧ (p2 ∨ p4)) ∨ ((p1 ∧ p1) ∨ p3)))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44658453187370291464281776305 : ((((p3 ∧ (((False ∨ True) ∧ p1) → p2)) ∨ (((p3 ∧ p2) ∧ (p2 ∧ (p1 ∨ ((p4 ∧ p2) ∨ (p3 ∨ True))))) ∧ (p4 → p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257570231808535875632881986047 : ((p3 ∨ p1) → (((((False ∧ ((p4 ∧ (p3 ∧ p3)) ∨ p2)) ∨ (p1 ∨ p3)) ∨ True) ∨ p5) ∨ ((p4 ∧ (False ∨ (p2 ∨ (True → p3)))) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50704495798984059204914021910 : ((((p4 ∧ True) ∧ ((p5 → (False ∨ True)) ∨ (True ∨ ((False → p5) → (((False → True) ∨ True) ∧ p1))))) → (p1 ∧ (p3 ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183958257672380436446856288465 : (((True → (p2 ∨ (((p5 → p2) ∨ (False → p1)) → p2))) ∧ p4) ∨ ((p2 → (((p3 ∧ p2) ∨ p1) ∨ p4)) → (((False → p1) ∨ p2) ∨ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782874964236815171182626654867 : (((p3 ∨ ((p3 → (True ∧ (p2 → ((p4 → (((((p1 ∧ p2) ∨ (p5 ∨ (p2 ∨ True))) → True) ∧ (False ∧ p1)) ∨ False)) → p5)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54793529865180561010028679416 : (((p5 ∧ ((p1 ∧ False) → (p3 → (p5 → p3)))) → ((((((p3 ∧ p2) → (p4 → (p1 ∧ False))) → p4) ∧ p1) ∧ (p2 → p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45554452057334450448780928919 : (((p2 ∨ (((p1 → ((((p5 → True) → (False ∨ p1)) ∨ (p5 ∧ False)) ∧ ((p5 ∨ p2) ∨ p1))) ∨ p2) ∧ (True ∨ (p2 ∧ p2)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190913890345453540860285064386 : (((p5 → ((p4 → p5) ∨ (p2 ∨ p3))) → (p3 → False)) ∨ (((p1 ∧ p4) ∨ True) ∨ (((p1 → p4) ∨ ((True ∧ (p2 → p4)) ∧ p1)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148225927260150591666872636195 : ((((p5 ∧ ((p5 → ((p3 ∨ p5) ∧ p3)) ∧ ((p2 ∧ p1) ∧ (p5 → p3)))) ∨ p1) ∨ (p2 → (True ∧ p2))) ∨ ((p1 ∨ p1) ∧ (p3 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156607960015569120406848155474 : (((((p3 ∧ p1) ∨ ((True ∨ p2) → (p4 → (((p1 ∨ p3) → (False → p4)) → p1)))) ∧ p1) ∧ p3) ∨ ((p4 ∨ ((p5 → p5) ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225738172999233048083903205178 : (((p4 → p2) ∧ p2) ∨ (((p4 → False) ∧ ((p4 ∧ True) ∨ (((True ∨ True) → False) ∧ (True → False)))) ∨ (p1 → (p4 → (p4 ∨ (p5 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147428701554884227237311114243 : ((((p2 → (False ∨ False)) ∨ ((p3 → False) ∧ (False ∧ (p5 ∨ (p2 ∨ (p5 ∨ ((p5 → p4) ∨ p5))))))) ∨ False) ∨ ((p2 → True) ∨ (p2 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669500297604695061623100106411 : ((((((False → (p2 → ((False ∧ True) ∨ (p1 ∧ (p3 ∨ (False → p1)))))) ∨ ((p2 ∨ p1) ∧ True)) → (p5 ∧ p5)) ∨ ((False → p4) ∨ p4)) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46612063247314789815051614363 : (((p2 ∧ (p3 → (((p2 ∨ p4) ∧ p4) ∧ (True ∧ ((p3 ∧ (p2 ∨ (False → (((False → p4) → p4) ∧ p5)))) → p1))))) ∧ (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136655908989959901087735990406 : (((p1 ∧ (False → p2)) → (((p5 ∨ ((p1 → ((True ∨ ((True ∨ p1) → p5)) → (p5 → p4))) ∨ p5)) ∨ False) → p5)) ∨ (p3 → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232149054071341082249149229130 : (((True → p1) → p3) → ((((((((p1 → True) ∧ (p4 ∨ p3)) ∨ (p2 ∨ p4)) → False) ∨ True) ∨ ((p2 ∧ (p5 → p5)) ∨ p2)) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667808431307713647299012803509 : ((((False ∨ (((p1 ∧ ((((False ∧ p3) ∨ p1) ∨ ((p3 ∨ (False ∨ p3)) ∧ (True ∧ p1))) ∧ False)) ∨ p4) ∧ p1)) ∧ ((False ∧ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752485118629868773322677283759 : (((False ∧ (((p5 ∧ True) ∨ ((p3 ∨ p4) → (((False → p3) → p3) ∨ ((False ∨ ((False ∧ p5) ∨ (p3 ∧ p5))) ∨ (p4 → True))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225200510303877189096011252571 : (((p4 ∧ p4) ∧ p5) ∨ (((p3 → (p1 ∨ (((p5 → ((True → p2) → p5)) ∨ p3) → p2))) ∨ ((p2 ∧ p1) ∨ ((p2 → p4) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40811497162169521634090477017 : ((((p2 ∨ (p5 → (((((p3 ∨ True) → ((True ∧ p1) ∧ ((p2 ∧ ((p1 ∨ p4) ∨ p4)) → True))) → p1) ∧ p4) → p4))) → p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147267007307554850048769354968 : ((((((p5 → p3) ∧ (False → (p5 ∧ (False → ((p1 ∨ True) ∧ ((p1 ∨ False) ∨ True)))))) → p1) ∨ p1) ∨ p2) ∨ (True → ((False → False) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803605532988927823288373699901 : (((p3 → (((p4 ∨ (p5 → p1)) ∧ (p3 → ((p1 → ((p2 ∨ p2) ∨ (p4 ∧ p4))) → (((p5 ∨ (p4 → False)) → p2) ∧ p2)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178629176584291500589143818121 : (((((p4 ∧ p1) → p2) ∨ (p5 ∧ p4)) → (p4 → (False ∨ (p2 ∨ p1)))) ∨ ((p5 ∨ (False → (p1 → (p3 → ((p5 → p1) → p1))))) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615744125544912469865913378953 : (((((p5 ∧ (((True ∧ (False → (p2 ∨ (p5 ∧ p5)))) → (p1 ∧ p5)) ∧ False)) ∧ (False ∧ ((p2 ∧ (p5 ∨ (True → p5))) → p4))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48207566511638464272905654550 : ((((True ∨ p2) → (False ∨ (p3 ∧ ((True ∨ p2) ∨ ((p1 ∨ p5) ∧ (p4 → ((False ∨ p3) → ((p2 → p2) → p3)))))))) → (p4 ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119335375612299630660278121867 : ((p3 → ((((True → False) ∨ p2) ∧ p4) ∧ ((((p5 → p3) ∧ False) ∨ (False ∧ p1)) ∧ ((p4 ∧ p4) → (False ∨ (False → p4)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153206582205922091699867524524 : ((True ∨ (((((p3 ∨ (p5 → p5)) → (p1 ∨ ((False → True) → p3))) ∨ p5) → (p2 ∨ p2)) → (p1 → False))) → (p4 ∨ ((p4 ∨ p1) ∨ True))) := by
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
theorem thm_5_vars_622087412050948865914691096382 : ((((p2 ∧ ((((p1 ∧ p5) → p5) → (p4 ∨ (p3 ∨ (False → (((p2 ∨ False) ∧ (p5 ∨ p5)) → p3))))) ∧ (p5 ∨ (True ∧ p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307763358329297424375778224764 : (p1 ∨ (p3 → ((False → p2) → ((((p1 → (p4 ∨ (p3 ∧ p5))) ∨ (p1 ∧ (True ∨ (p3 → (False → (p5 → p2)))))) → False) → (p1 → p5))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → (p4 ∨ (p3 ∧ p5))) ∨ (p1 ∧ (True ∨ (p3 → (False → (p5 → p2)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149065532829182562605940590643 : ((((p4 → p4) ∧ p5) → (((p4 ∨ (p4 ∨ (((p2 → (p1 ∨ True)) ∧ p4) ∧ (True ∧ p1)))) ∧ False) ∨ True)) ∨ (False ∧ ((p2 ∧ p3) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_317738005139428270836429815174 : (p4 ∨ ((((p1 ∨ ((p2 → (False ∧ p4)) → (p2 → (False ∧ (((p2 ∨ p1) ∧ (p3 → True)) → p4))))) ∨ False) → (p2 → (p1 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225629711975339377687833381780 : (((p1 → p4) ∧ False) ∨ (((p4 → (p4 → p2)) → (p4 → (((p3 ∨ p3) ∨ (p5 ∨ (p1 ∨ True))) → p3))) → (p2 ∨ (p4 → (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_54453963396946367960927609143 : (((((True → (p5 ∧ p1)) → (True ∧ p3)) → p2) ∨ (((p3 → p5) ∨ ((p4 → False) ∨ (p3 → ((p2 ∨ p5) ∧ (True ∧ True))))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722989891256070891246144911000 : (((((False ∨ True) ∨ True) ∧ (((p4 ∧ ((False ∨ p5) ∧ p5)) ∨ (((False ∨ p4) → p3) ∧ (((p3 → p3) ∨ p1) → (p4 ∧ p4)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5098687997465212910666281473 : (((((p4 ∨ ((p3 ∧ ((p3 → p4) → p1)) → (p4 ∨ p1))) ∨ (p1 → (((p2 ∧ p4) → ((p3 ∨ p4) ∨ p3)) → True))) ∨ p5) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184355248990252351608402216874 : (((True ∨ ((p3 → p4) ∧ ((False → p4) ∧ (p3 → p3)))) → p2) ∨ (((p4 ∧ p3) ∨ True) ∨ ((((p5 ∨ p5) ∧ p1) ∨ True) ∧ (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48641315404722405221625987575 : ((((p5 ∧ ((((p3 → p4) → False) → (p5 ∧ (p3 ∧ (p1 ∧ (p3 → p5))))) ∨ p5)) → (p3 ∧ (p4 ∧ p3))) ∧ ((False ∧ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38024292443668870062617989752 : ((((p3 → ((p3 ∧ ((p1 ∧ p2) ∨ p5)) ∨ (True ∧ (p4 ∧ (False ∧ (p3 → ((p3 ∨ (p4 ∧ False)) ∧ p5))))))) ∨ (False → p1)) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345639715038054971346151863913 : (p3 → ((p2 ∧ (p1 ∧ ((p5 ∧ (((p4 ∧ (False ∨ p2)) → p5) → p4)) ∧ (((p3 → False) → (p3 ∨ ((True ∨ p3) ∧ False))) ∨ p1)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730337730869551569490954095140 : (((((p5 → p4) → True) → ((p3 → p4) → ((p1 ∧ (((p4 ∧ False) ∨ p4) ∨ (p2 ∧ (False ∧ (p2 → p5))))) ∨ (True ∨ (p1 → p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618528038891156688856949818368 : ((((((p1 ∨ False) → (False ∧ p5)) → (((False → p4) → (((p1 ∧ ((p5 ∨ (p5 ∧ p1)) ∨ False)) → (p3 ∧ p1)) ∨ p3)) ∨ p4)) ∨ p1) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h3.left
  let h19 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706995242735594252396557675312 : (((((False ∧ ((True → (p5 ∨ p3)) → False)) ∨ p1) ∨ (p3 ∨ (p5 → (p1 → (((p4 → p1) ∧ ((p4 → False) ∨ True)) ∧ (p1 ∨ p3)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60631665278491543883484628791 : ((True ∧ (((p4 ∨ (True → ((((p2 → p5) ∨ p4) → ((p1 ∧ (False → (p3 ∨ p3))) ∨ p1)) ∧ p5))) ∧ False) ∧ ((p5 ∧ p4) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48598685902383355697845869360 : ((((((((((p1 ∨ p4) → (((True → p5) → True) ∨ True)) ∧ p3) ∧ p2) → p2) ∧ p1) → p5) ∨ (p1 ∨ p3)) ∧ ((True → p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654646266775316533726008779261 : (((((((p3 ∨ (((p2 ∧ p1) ∧ ((True ∨ (True ∧ True)) ∨ p2)) ∨ (False ∨ ((p1 → p4) ∨ p1)))) ∧ p1) ∧ p4) → False) ∨ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49315947503772502071438682823 : (((p2 ∨ (True → (p2 ∧ (((p4 → p3) ∧ ((p4 ∧ (((True ∨ p5) ∧ p5) ∨ p5)) ∧ (p1 ∨ p3))) → False)))) ∨ ((False ∧ p4) → p2)) ∨ p3) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781775768419153374887197976855 : (((p2 ∨ (p5 ∨ (p2 ∨ ((p2 ∨ p5) → (((((p2 → (p4 ∨ False)) → p4) → (False ∨ p3)) → p3) ∨ ((False ∨ False) → (False ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300113098722611730256912111229 : (False ∨ (((((p3 ∨ True) ∨ p1) ∧ (p5 → p3)) ∧ ((p2 ∨ (p1 ∧ (p4 ∧ True))) → (p3 ∨ ((p4 ∧ (p4 ∨ False)) ∨ p1)))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807347801615629416674584503248 : (((p4 → ((p3 ∨ (p2 ∨ (False → (p1 ∧ (p5 → (p2 ∨ (p1 ∧ p3))))))) → ((p2 ∨ (p4 ∧ p2)) ∨ (p5 → ((p4 → p1) ∨ p5))))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196779315752460847583275807738 : ((((p5 ∧ True) ∧ ((False ∧ False) ∨ p4)) ∧ p5) ∨ (True ∨ (False ∧ ((p1 ∧ ((p4 ∨ ((False → True) ∨ True)) ∨ p5)) → (True ∧ (p4 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219802275926326438804353665119 : ((p2 → (True → (False ∨ False))) → (((((p1 → (False → p3)) ∧ (p4 ∧ False)) ∨ True) ∧ p5) → (p1 ∨ ((p3 ∧ (p1 ∧ (p1 ∧ p3))) ∨ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667047054961775535514699274679 : ((((((p2 ∧ False) ∧ p1) ∧ ((((((((p2 ∨ p4) ∨ p5) → (p4 ∧ p2)) ∨ p2) ∨ p3) ∨ p2) ∧ p3) → p5)) ∧ (False ∨ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148301916919626909824311949316 : ((((p3 → (p5 ∨ p1)) ∧ ((True ∨ (True ∨ p5)) → (p4 ∨ (p4 → (p2 → p1))))) → (False ∨ (p5 ∧ p5))) ∨ (((p2 ∧ p1) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323223246385807931319309612431 : (p5 ∨ ((((((((False → True) → p2) ∧ p5) → p1) ∨ False) ∧ p3) ∨ ((p3 ∨ (p2 → (((p2 ∨ p5) ∧ p3) → p4))) ∨ False)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556935695385155628908254426265 : (((p3 ∨ ((((p3 ∧ (p2 ∨ p4)) ∨ (((p3 → (p1 ∨ True)) ∧ p4) ∨ True)) → p1) → ((p1 ∧ (p2 → (p2 ∧ p1))) ∨ (p3 → p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149485177325652427038778642161 : ((p1 ∧ ((((p4 ∨ p5) → (p5 → ((((True ∨ p5) → (p5 ∧ p1)) → (p2 ∧ p3)) → False))) ∧ p4) ∧ p5)) ∨ (((False ∨ True) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150284604849055652591511053327 : ((p4 → ((((p5 → (p5 → ((p4 → p4) → ((False → p4) → (p3 ∨ False))))) → (p4 → p1)) → False) ∨ p4)) ∨ (((p5 → p2) ∨ False) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4190064025670481275420489485 : (p4 ∨ (p2 ∨ ((p2 → (False ∨ (((True ∨ True) → ((False ∨ (p5 ∧ p5)) → (p1 ∨ (p3 ∨ True)))) ∨ ((True → True) ∨ p5)))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352040566958574559125808065959 : (p4 → (((p4 ∧ p4) → (p5 ∧ ((True ∨ False) → False))) → (((p2 ∨ (p1 ∨ p3)) ∧ (False ∨ False)) ∧ (((False ∨ p5) ∨ (True → False)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p4 ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354768796550939693120106906871 : (p5 → (((((True ∨ p1) → (False ∧ p3)) → (((True → False) ∧ p1) ∧ False)) → ((((p3 ∨ (True ∨ (p1 → True))) ∨ p5) → p4) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97727517698192312986276611317 : ((p3 ∨ ((((p2 ∧ (p3 ∧ (False → p4))) → (False ∨ (p4 ∨ p2))) ∨ True) → ((p3 → True) ∧ ((True → (p3 → (p1 → False))) ∧ p3)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p2 ∧ (p3 ∧ (False → p4))) → (False ∨ (p4 ∨ p2))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19795727391662929227786459397 : ((((p3 → ((p1 ∨ (p3 ∨ (p4 ∨ (True ∧ p5)))) ∨ True)) ∨ ((p3 ∧ p2) → False)) → ((((False ∧ True) ∨ p1) ∨ p2) ∨ (False → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337773018731831292885434000526 : (p1 → (((p3 ∨ (p2 → p3)) → ((((p3 ∧ (False ∧ True)) → (p2 → False)) ∨ p3) ∧ False)) ∨ (((False ∧ (p4 → p2)) ∨ (True ∨ p3)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138260821235172766114943557088 : ((p2 → (p1 ∨ ((((p2 ∧ (((((p3 ∧ True) ∨ p5) ∧ p5) ∧ p4) ∧ p5)) ∨ True) ∧ p3) ∧ ((p5 ∨ p1) → True)))) ∨ ((p5 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245213186437063392270265613231 : ((p2 ∧ False) ∨ (p5 → (((p1 ∨ (True ∨ (p1 → (((((p3 → p5) ∧ (p4 → p2)) ∨ True) ∧ p5) → p2)))) → ((p3 ∨ p1) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613038935972735517088742988362 : (((((((((p1 ∧ (p4 ∧ (p5 → ((False ∧ (False → p1)) ∨ p4)))) ∧ (p1 ∧ True)) → (p5 ∨ p5)) ∨ p5) ∨ p1) → (False ∨ p4)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120953542123311917682940269880 : ((((p2 → (p5 ∨ p5)) ∧ (((p3 ∨ (((((p1 ∧ True) ∧ (True → p4)) → False) ∨ True) → (p1 ∧ p3))) → p5) ∧ p2)) ∨ p1) → (p1 ∨ p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32537423046434127406855758103 : ((p2 ∨ (((p2 → p3) ∧ (((False → p1) ∨ (True ∨ p1)) ∧ (p2 → ((p5 ∧ True) ∧ ((p4 ∧ p2) ∧ p4))))) → (p3 ∨ (True ∨ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59198028905538307936819153402 : (((p1 ∨ p2) ∨ (((((True ∧ False) ∧ (((p2 ∧ p4) ∨ True) → ((False → (((p5 ∨ p1) ∧ p5) ∨ p2)) ∨ p1))) → False) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728039414600576273321045263785 : ((((p4 ∨ (p1 ∧ p2)) ∨ (((p4 ∨ (p3 ∨ p3)) → ((p5 ∨ p5) → p2)) ∧ (True ∧ (p4 → ((p4 → (p4 → p1)) ∧ (p3 ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50562489269814184159219695427 : ((((((p5 ∧ ((True → True) ∧ ((False ∨ p5) ∨ p4))) → (p5 → (p4 ∧ (p4 ∧ p4)))) ∨ False) → p4) → ((p5 → (p5 ∧ True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121224480336347734698653149737 : (((p1 → ((((p1 → p5) → (p5 → p3)) ∨ (p4 → ((False → True) → ((p4 ∧ (False ∨ False)) → p1)))) ∧ (p2 → True))) ∨ p3) → (p3 ∨ True)) := by
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
theorem thm_5_vars_152223786796467734757604341335 : (((p1 ∧ ((p3 ∨ (p4 ∨ p2)) → p3)) ∧ (((True → p1) → p3) ∨ ((False → (p3 ∨ (True ∧ p2))) → p2))) → (True → ((p5 → p4) ∨ True))) := by
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
  cases h4
  case inl h7 =>
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
theorem thm_5_vars_116370356530503749047898492866 : ((((False ∨ False) → p5) → ((p5 → p4) → (p4 ∨ ((p5 ∧ p2) ∧ ((False ∨ True) ∧ (((False ∨ p4) ∨ (False → True)) → p4)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197303487163608630143374051180 : ((((True ∨ p2) ∧ (p3 ∨ (False → p2))) → p3) ∨ ((((p3 ∧ p1) → ((((p3 ∧ p1) ∧ True) → (True → (p1 ∨ p4))) ∧ p3)) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587394296142807131621479110701 : (((((((((((((p4 ∧ p2) → p2) → True) ∧ p3) ∧ ((p4 → p3) ∨ p4)) ∧ (p5 → (p4 ∧ True))) ∧ p5) ∧ p5) ∨ True) ∨ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611209461983091456120051190775 : ((((((True ∧ p1) ∧ ((p3 ∨ (p5 ∨ (((((p5 ∨ True) ∧ ((True → p5) ∧ p2)) ∧ p2) ∨ p2) ∧ (True ∨ p3)))) ∧ p3)) → False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159631108090248344530320534528 : (((((((False ∧ ((p2 ∧ p5) → p3)) → (((True → p1) ∨ p5) ∨ p3)) → p4) → p5) ∨ p3) ∨ p3) → ((p5 → p4) ∨ (False → (p4 ∨ p4)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85983445112777767372642715155 : ((((False → (((p1 → p1) ∧ p2) ∨ True)) → (p2 ∧ p5)) ∧ (p3 → ((p5 → (p5 ∨ (p2 ∧ False))) → (p4 ∧ ((p1 ∨ False) → p1))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → (((p1 → p1) ∧ p2) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186348552863908883962343289865 : (((((p3 → p4) → p2) ∨ (False → (p3 ∨ (p4 ∧ p1)))) → False) → ((p4 ∧ (((p4 → ((p2 ∧ p1) → p5)) ∨ p4) → (p1 ∨ p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p4) → p2) ∨ (False → (p3 ∨ (p4 ∧ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68939252535838290430064527217 : ((p4 → (p5 ∨ ((p3 ∨ ((((p1 → p5) ∨ p1) ∧ (p3 ∧ ((p3 ∧ False) ∨ (p2 → p4)))) ∧ (p2 ∨ True))) ∧ ((p3 ∧ p2) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173502766182588633785052413227 : ((((False ∨ ((p4 → (((p5 ∨ False) ∧ p4) → p3)) ∧ True)) ∧ (True → p4)) ∧ p3) → ((((p2 ∨ (p5 ∨ p1)) → (p1 ∧ p1)) → p2) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653635795843512220700752076489 : (((((((True ∨ ((p4 → ((p5 → p3) → True)) → (p5 ∨ (p4 ∨ p4)))) → (p3 ∨ (p5 ∨ (p2 ∨ False)))) ∨ p2) ∧ p2) ∨ (p4 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_692983739514581307836092581224 : (((((p4 ∧ True) → ((p4 → p1) ∧ (((p2 → (p3 → p1)) ∧ p2) ∨ p1))) ∧ (((p5 ∧ p3) → (p2 ∨ (p3 → (p5 ∨ p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136420421606347898946991299690 : (((((p5 ∨ True) → False) ∨ p2) → (False ∧ (p4 ∧ ((p5 ∨ p3) ∧ (((p2 ∧ (True ∨ (p3 ∨ p3))) ∧ True) ∨ p3))))) ∨ (True ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198089673329891342416613555290 : (((p5 ∨ p5) ∨ ((True → (p3 ∨ p3)) ∨ p2)) ∨ (p1 → (((p2 ∨ p3) → p1) → ((False ∧ True) → (p4 ∨ ((p5 ∨ p3) ∧ (p5 → False))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634149842759003333417574930276 : (((((((p3 → p5) ∨ False) → (((p3 ∨ ((p1 → p5) ∨ p3)) ∧ ((True ∨ p2) → p4)) ∧ ((p5 → p3) ∧ p1))) → (p5 → False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159195103501045438693879834779 : ((p2 → (((p2 ∧ p3) ∨ (((p5 ∨ (p3 ∧ p5)) ∨ ((p3 ∧ False) → (p4 → False))) ∧ p1)) ∨ p2)) ∨ (False → ((p2 ∧ p1) ∧ (p1 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



