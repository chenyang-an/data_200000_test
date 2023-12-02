variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218043247251314782436818609577 : (((p2 ∨ p2) ∧ (p2 ∧ p3)) → (((p4 ∧ p1) ∨ (p3 → p2)) ∧ (p4 ∨ (True ∨ (((p5 → ((p2 → False) ∧ p3)) → (False ∨ p4)) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722235663529811168134993108219 : ((((p5 → (p4 ∨ (p4 → p3))) → (((True → False) → ((p4 ∨ p1) ∧ ((p2 ∨ p4) ∨ ((p3 ∧ p5) ∨ ((p2 ∧ True) ∨ p5))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193024471764378237235543098356 : ((((p3 ∨ p2) ∨ ((True ∧ p4) ∨ p2)) → (p5 → False)) → ((((p1 → p2) ∨ ((False → ((False ∨ (p5 → p5)) → p4)) ∧ p2)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49052721092682148561120683142 : ((((((p2 ∨ p2) ∨ (((False → True) ∧ p1) ∧ p2)) ∨ ((p4 ∧ (p5 ∧ p1)) ∨ (p2 ∧ p5))) ∧ (p1 ∧ False)) ∨ (p5 ∨ (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58947956805686067464155903799 : (((p2 ∧ True) ∨ ((((True → True) ∨ (p4 ∨ False)) → False) ∨ (((p2 ∨ ((((False → p5) ∨ p3) ∧ p5) ∧ False)) ∧ False) ∧ (False → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190399804412614349370104994667 : (((p3 ∧ (((True ∨ p1) ∧ (p5 ∨ False)) → p4)) ∨ False) ∨ (((((((p2 ∧ p5) ∧ False) ∧ ((p2 → p3) ∨ False)) ∧ p2) ∧ p2) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315834860551453557146872727767 : (p3 ∨ ((True → False) → ((p2 ∨ p4) ∨ (((p4 ∧ ((False ∨ p5) ∧ p1)) ∧ (True ∨ p3)) ∨ (((((True ∧ False) → p5) ∨ p3) ∨ p1) ∧ p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800815801860703942124807495857 : (((p2 → (((((p2 → ((p1 → ((True ∧ (((p3 ∨ p3) ∧ False) → False)) → p3)) ∨ (p4 ∨ p5))) ∨ p4) ∨ p3) ∧ p4) ∨ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680646871701837650166519228126 : (((((((True ∧ True) → p3) ∨ (p2 → p3)) ∨ (((p4 ∨ False) ∨ (p5 → ((p2 ∨ p2) → False))) ∧ p2)) → (False ∧ ((p2 ∨ False) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117852940677270483660861258513 : ((p5 ∧ ((((p2 ∧ (((False ∨ p1) ∧ (p4 ∨ ((p3 ∧ p2) ∨ (p5 → ((p3 ∨ p2) → p2))))) ∨ p1)) ∧ True) ∨ False) ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148244308289956675642362267575 : ((((True ∧ (False ∨ ((False ∧ False) → True))) → (((p4 ∧ False) ∧ (p1 → p3)) ∨ p5)) ∨ ((p2 ∨ True) ∨ p1)) ∨ (((True ∨ p3) ∨ p1) → p5)) := by
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
theorem thm_5_vars_191381427306893845378211775901 : (((p3 → p2) ∨ (((p2 ∨ (True → p5)) → p3) → p4)) ∨ ((p1 ∧ (((p2 ∨ False) ∨ p3) → (p1 ∨ p1))) ∨ ((p5 ∨ (False → p1)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_168068558425367557846620153265 : ((((p3 ∨ p3) ∧ (True ∧ p3)) ∧ (p2 ∧ (p4 ∧ (p5 → ((p2 ∧ (True ∨ p5)) → p3))))) → (((True → p5) ∨ (False ∨ (p4 ∧ True))) ∧ p3)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h18
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h21.left
    let h28 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h23.left
    let h33 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h21.left
    let h35 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173724609028006546689387334469 : (((((p5 ∨ True) ∨ ((False ∨ p3) → ((False ∧ p4) → True))) → (p2 ∨ p1)) ∨ True) → (True → (((p1 ∧ (False ∨ (p5 ∨ p2))) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191912021548835036690306357255 : ((p5 ∨ (p3 ∧ (((p3 ∧ (False ∨ False)) ∧ False) ∨ p1))) ∨ (False → (((((p5 ∧ True) ∨ True) ∧ p4) ∨ (p5 → ((p5 ∨ p5) → False))) → p4))) := by
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
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h1
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192806533716689107945780245882 : (((True → ((p1 ∨ p1) → ((p4 ∨ p5) → True))) → False) → ((p3 ∨ False) ∧ ((((False ∨ p2) → (p5 → (False ∧ (p2 → True)))) ∧ p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((p1 ∨ p1) → ((p4 ∨ p5) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (True → ((p1 ∨ p1) → ((p4 ∨ p5) → True))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h11
    -- False on the left can always be used.
    apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (True → ((p1 ∨ p1) → ((p4 ∨ p5) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h17
  -- False on the left can always be used.
  apply False.elim h21
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h22 : (True → ((p1 ∨ p1) → ((p4 ∨ p5) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h26 := h1 h22
  -- False on the left can always be used.
  apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175502893793664521500057360315 : ((p3 → ((((False → p2) → p1) ∨ p3) → ((p4 → (p5 → p5)) ∨ (p3 ∨ p5)))) → ((p2 ∨ ((p1 → p4) → p3)) ∨ (p2 ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54645944487223220125289122730 : (((((p3 ∨ ((p2 ∨ False) ∨ p5)) ∧ p2) ∨ p3) → ((p4 ∨ (p4 ∨ p1)) → (p1 ∨ ((((False ∨ p4) ∨ p2) ∨ (True → p1)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207655334615336034468716369494 : ((((p5 → p5) ∧ (p3 ∧ True)) → p1) → (((p1 ∨ p1) ∨ p2) ∨ (p3 → ((p5 ∧ (((False ∧ (p4 ∨ p4)) ∧ p3) ∧ True)) ∨ (p1 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345615570837619170114578158429 : (p3 → (((False → False) → (((p4 ∨ (p3 → ((p5 → p1) ∨ p3))) ∧ (p3 ∧ p3)) ∧ (p4 ∨ (p3 → ((p2 → (p1 ∧ p3)) ∧ p1))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64367400246237164305123662096 : ((p1 ∨ (((True ∨ (p3 → (p1 → (p1 ∧ p5)))) → (p1 ∧ ((p1 ∨ ((((p1 ∨ p4) → p1) ∧ (p3 ∨ p3)) → True)) → True))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314642211358503036682734965582 : (p3 ∨ ((((((False ∧ (False ∨ p3)) → (p3 ∧ (p3 → p2))) ∨ p5) → (p1 ∨ False)) ∨ True) ∨ (p5 ∧ (((False ∨ (p2 → p4)) ∧ True) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317825464122305206807950758751 : (p4 ∨ (((((p3 ∨ p3) ∨ p3) → True) → (((p2 ∨ ((True ∨ p2) → (p4 → True))) → (p4 ∧ (False → (p2 ∨ p5)))) ∨ (p4 ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718361302661541039679898106828 : ((((((True → False) ∨ p4) → p3) ∨ (False ∧ (p2 ∧ ((p2 ∧ (False → (p3 ∧ (p1 → p2)))) → (p4 ∨ ((False ∨ (True ∧ p5)) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50814578802918583035230774703 : (((p4 → (((True ∧ (p1 → p3)) ∧ (((False ∨ p1) ∧ True) → (p2 → ((False ∧ p4) ∧ False)))) ∨ p4)) → (((p4 → p5) ∧ p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64253673018678608786098548358 : ((False ∨ (p3 ∨ ((p5 ∧ p1) → (((True ∧ (p1 → False)) ∨ p3) → ((((True ∧ ((p4 ∧ p4) ∨ (p5 → p4))) ∧ p4) ∨ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224113231043816619282629860699 : ((p5 ∨ (False → p2)) ∧ ((p4 → (True → False)) ∨ ((True ∨ (p2 → p2)) → (p5 ∨ (p4 ∨ ((p2 ∧ False) → ((p4 → (p1 → p5)) ∨ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56801430841266401693946854360 : ((((p1 ∨ p3) → p5) ∧ (((p3 ∨ (p4 ∧ True)) → ((p5 ∧ ((p1 → (p2 → True)) ∧ (True → p5))) ∨ ((p2 ∨ False) ∨ False))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114622680227414602832649833801 : (((((False ∨ (p1 → p3)) ∧ (p1 ∨ (p5 → ((True ∧ p5) → (p1 ∨ p1))))) ∧ p5) ∨ ((p2 ∧ p4) ∨ (p2 → (p5 → True)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638350048966245431712646024163 : (((((((p1 ∨ p1) ∧ False) → (p5 ∨ p4)) ∧ (((p5 ∨ (((p1 ∨ p4) → p5) → p3)) ∧ (p4 → p4)) ∨ ((p4 ∧ p5) ∨ p4))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734566401809987996630448038412 : ((((p1 ∨ p2) ∧ ((((((p5 ∨ ((((p4 ∧ True) ∧ (True ∧ (p4 → True))) ∨ False) ∧ p2)) ∨ p5) ∨ (False ∧ True)) ∧ p5) ∧ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341062669628545020179750102558 : (p2 → ((p3 ∨ (p1 → ((False ∧ (p4 ∨ (((p3 → False) ∨ False) ∧ (p3 ∧ (False ∨ (p1 → (p4 → (False ∨ (p5 → p4))))))))) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60723250315005312510576774982 : ((True ∧ ((((p3 ∨ p3) ∨ p2) → p4) ∧ ((((p2 ∧ (True ∧ p3)) → p5) ∧ (p4 ∨ p5)) → (((p3 → (p4 → p5)) ∨ p2) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664261629993750145933619582525 : ((((p1 ∨ ((p3 → p5) ∨ (p2 → (p2 → (p1 ∧ (p5 ∧ (((True → p1) → True) → ((p5 ∨ (p5 ∨ p5)) → False)))))))) → (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115208950353954453293872394526 : (((p5 ∧ (p1 ∨ (p3 ∧ (p5 → (p3 ∧ (p4 ∨ True)))))) ∧ ((p2 → ((p4 ∨ p2) ∨ False)) → (p3 ∧ (True ∧ (p2 ∨ p5))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253726117872646834053569673178 : ((p1 ∧ p1) → ((p4 ∧ (((((True ∧ p5) ∨ p4) ∨ True) ∨ (((p5 ∨ (p1 ∨ True)) ∧ True) → p4)) ∧ (p4 ∨ (False ∨ (p5 ∨ True))))) ∨ p1)) := by
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
theorem thm_5_vars_59393497893220902300108119950 : (((True → p1) ∨ (p3 ∧ (((p4 ∧ p2) ∨ p2) ∨ (((p3 → (((False ∧ p2) ∨ p3) ∧ ((p5 ∨ False) ∧ p5))) ∧ True) → (True ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60298269155275678021044115820 : (((p1 → p1) → ((p4 ∨ p5) ∨ (((p4 ∨ p3) ∨ (p2 ∧ ((p1 → (p3 ∨ p3)) ∧ p3))) → ((False ∨ True) ∨ (p1 ∧ (True ∨ False)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160531374062993751034347424999 : ((((p5 → (((p3 ∨ True) ∨ (p1 ∨ p1)) ∧ p1)) → (p2 → p4)) ∨ (p2 → (p2 ∧ (p2 ∧ p2)))) → (((p4 ∧ p3) ∨ True) ∧ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40377477655703053909868435176 : ((((((p5 → (p3 ∨ ((((p1 ∨ (True ∧ p4)) ∨ p1) ∧ p2) ∧ p4))) ∧ ((p1 ∨ p4) ∧ (False → p1))) ∧ (True → p5)) ∨ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205322068670041748325681371338 : (((p5 ∨ (p2 → p5)) ∨ (p3 ∧ p5)) ∨ ((True ∧ (False → p4)) ∧ (p5 → (((((p3 ∧ ((p4 ∨ p5) → True)) ∨ True) ∨ p2) ∧ True) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351823778182563662868180474684 : (p4 → (((p3 → (p1 → p4)) → ((p5 ∨ (True → (p1 ∨ True))) ∧ p3)) ∨ (p4 → ((p5 → ((p5 → (p1 ∨ p4)) ∨ p4)) ∨ (False ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171876206926625361636607311488 : (((p4 ∧ ((p5 ∨ p1) ∧ (p3 → ((p2 ∧ p2) ∧ ((p3 ∧ p2) ∨ p5))))) → False) ∨ (((p3 → (p3 → p4)) ∨ True) ∨ ((p2 → p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111658103242551357167357966899 : ((((p2 ∧ (((p3 ∧ (((p1 ∧ p3) ∧ (p4 → p5)) ∨ p4)) ∨ (p1 → (((False ∨ True) → p4) ∨ True))) ∧ p4)) ∨ p3) ∨ True) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304751733770527626964737082439 : (p1 ∨ (((p2 ∧ False) ∨ (((p4 ∧ p2) ∨ p5) ∨ ((p5 → (p4 ∧ (p5 → ((p1 ∨ p1) ∧ (p2 ∨ (False ∧ p4)))))) ∧ p5))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194025566448592369740197827584 : ((p4 ∨ (p3 ∨ (((False ∧ False) → p2) ∧ (p3 ∨ False)))) → (p2 → (((False ∨ (((p4 ∨ True) → p4) → False)) ∧ True) ∨ ((p2 → p5) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192471746836154950909964117202 : ((((((p2 ∧ p5) → p1) → p2) → (True ∨ True)) ∨ True) → ((p1 ∨ p1) → ((p5 ∧ (p5 ∧ ((p5 → p1) → (False ∧ (p2 → p2))))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h21 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h23 := h7 h21
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h26 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h28 := h7 h26
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625603120856126234163956802629 : ((((p1 → ((((p3 → ((True ∧ True) → True)) → (False ∨ (p2 ∨ (p2 → (p1 → (p5 ∧ p5)))))) ∧ (p3 ∧ (True → p4))) ∨ True)) ∨ p1) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37081598583346918426108404569 : ((((((((p2 ∨ (p5 ∨ p5)) ∨ p5) ∨ (p1 ∧ ((p5 ∧ p1) ∨ ((p1 → p1) → p3)))) ∨ ((p3 ∨ p2) ∧ p4)) ∨ True) ∧ True) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53199284097166716464396549641 : ((((False ∨ (p4 ∨ ((p4 ∨ p3) ∧ (p2 → p3)))) ∨ (p1 ∨ p1)) ∨ ((p3 → p5) → (True ∨ (((p1 → p3) → True) ∨ (p4 → False))))) ∨ False) := by
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
theorem thm_5_vars_169423120660098273535645182058 : ((((((p1 → (((p1 → False) ∨ p4) ∧ False)) ∧ p2) ∧ p4) ∧ (True ∧ True)) ∨ True) ∧ (p1 → (p1 ∧ (p3 ∨ ((p3 ∧ False) → (p4 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190265436790599236307864586111 : ((((((p3 ∨ p5) ∧ (p5 ∨ True)) → p4) ∨ p3) ∨ False) ∨ (((True ∧ ((False → ((False ∧ (p1 ∧ p3)) ∧ (p1 → True))) → False)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149586640818245586229576251493 : ((p3 ∧ ((p3 ∨ ((False ∨ ((p5 ∧ True) ∨ p3)) → (((p3 ∨ (p1 ∨ False)) → False) ∨ (p4 → p2)))) ∨ p5)) ∨ ((p3 ∨ True) ∨ (False ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42102373785657096107536019295 : ((((p1 ∧ p1) → ((((False ∧ p4) → p3) → False) ∧ ((p4 ∧ False) ∧ ((p1 ∨ (((False ∧ p4) ∨ (False → p5)) → True)) ∨ p2)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178500830635197923468657863061 : (((p1 ∨ ((p4 ∨ p3) ∧ ((p1 ∧ p3) ∨ p3))) ∨ (True ∧ (False ∨ True))) ∨ ((p5 ∨ False) → (((p5 ∨ False) ∨ True) ∨ (p4 ∧ (p2 → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_592279011787537932724592597249 : (((((((p1 ∧ ((p5 ∧ p2) ∧ (False ∨ (p2 → p4)))) → (p2 ∧ (p2 ∨ (False → (p3 ∨ (p2 → p4)))))) → p1) → (p4 ∨ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177921578834784359192232055893 : ((((((True ∧ p4) ∨ (p2 ∧ p2)) ∧ True) → ((False ∧ p2) ∧ False)) ∨ p3) ∨ ((p5 ∨ ((p3 → (p3 ∨ p3)) ∧ (p1 ∨ p3))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55404753842086619023015029520 : ((((((True ∧ p4) ∨ p3) ∨ p1) ∨ p5) → (((p5 ∨ (p4 → (p1 → (True → (((p2 ∨ p2) ∧ p2) → p1))))) ∧ p5) ∨ (p3 → p3))) ∨ p4) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325691439999825439118372039246 : (p5 ∨ (p1 ∨ (((True ∨ (p2 ∧ False)) ∧ ((((p4 ∧ False) ∨ ((p5 → p3) → p3)) → p1) ∨ (p4 ∨ p3))) → (((p5 ∧ p4) ∨ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233156709562727339557785330997 : ((p5 ∧ (p5 ∧ p4)) → (((p1 ∧ ((p3 ∧ ((False ∧ p3) → p2)) ∨ p3)) ∧ p1) ∨ ((p3 ∧ (True → ((p4 → p3) ∨ p5))) ∨ (p4 ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113213491830478029350668076966 : ((((False ∧ (((p2 ∧ p3) ∨ p2) ∨ (((p2 → (p1 → p1)) → (p5 ∨ ((p1 → p2) → True))) ∨ p3))) ∨ p1) ∧ (p5 ∨ True)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165793620592940245829552565449 : ((((p1 ∧ p1) ∧ True) ∧ ((True ∨ (True ∨ p3)) → (((p1 ∧ p2) ∧ (True → p1)) ∧ p4))) ∨ ((True ∧ (False ∨ (False ∧ (False → p1)))) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188374061163310013052040321673 : (((((p1 → (p1 ∨ (p1 ∨ True))) ∨ p5) → p2) → True) ∧ ((((p4 ∧ (p3 → p5)) → p4) → (p3 ∨ (p4 ∧ p3))) ∨ (p1 → (p2 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141461054134350278603279783877 : ((((p5 → p5) → False) ∧ ((p5 ∧ (((p5 → (p2 → (p1 → ((p1 → (p3 ∧ True)) → p3)))) → p3) ∨ p4)) → True)) → (p2 ∧ (p4 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257981077034724662009542509298 : ((p4 ∨ p1) → ((((p1 ∧ ((p5 → (p5 → False)) ∧ (p3 ∧ (p4 ∧ p4)))) → True) → ((((True → True) → (p2 → True)) ∨ p5) ∧ False)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 ∧ ((p5 → (p5 → False)) ∧ (p3 ∧ (p4 ∧ p4)))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 ∧ ((p5 → (p5 → False)) ∧ (p3 ∧ (p4 ∧ p4)))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55083887420476453652665302009 : (((False → (p1 ∨ (p4 ∧ (True → False)))) ∧ ((((p2 ∨ p1) ∧ ((p3 ∨ p4) → True)) ∨ ((p1 → p2) ∧ p2)) → ((p4 ∧ p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64402029165880782032511906268 : ((p1 ∨ (((((p5 ∨ p1) ∧ (p5 ∧ (p1 ∨ (p3 ∨ p4)))) ∧ ((True → True) → p1)) ∧ (((p1 ∧ (p1 ∨ p2)) → p4) ∨ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204150422652453840084718184103 : (((((False → False) ∧ p1) ∨ False) ∧ p4) ∨ ((((False ∧ False) ∧ p4) ∨ p4) ∨ ((p1 ∧ p2) → (((p5 → ((p1 ∧ p3) ∨ p5)) → p4) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217775002540759262335835963018 : (((True ∨ (p1 ∧ p1)) → p5) → ((((((True ∧ p1) ∧ (p2 → ((p4 → p1) ∧ True))) ∨ p1) ∨ (p3 ∨ ((False ∨ False) → p4))) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137835965377537224663430998795 : ((p3 ∨ ((p2 ∧ ((False → (p2 → True)) → (p4 ∧ (p1 → (True ∨ (p5 ∧ p3)))))) ∧ (True → ((p1 ∨ p4) ∨ p4)))) ∨ ((p4 ∧ False) → p4)) := by
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
theorem thm_5_vars_166225095641460751858338277806 : ((p2 ∧ ((False ∨ ((p1 ∨ p4) ∧ (p3 → (p5 → (p5 ∧ p5))))) → (True ∧ (p4 ∨ False)))) ∨ ((p1 ∧ True) → (((False ∨ p4) ∧ p1) → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51041350822188750295189471078 : (((p1 ∨ (((((p1 ∧ p3) ∧ p5) → p3) → ((p5 ∨ (False ∧ p3)) ∨ (p3 ∨ p1))) ∧ p1)) ∧ (p3 ∨ (((p3 ∨ p2) ∧ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150078772389418605513762804030 : ((True → ((p3 → p5) → ((((p1 → (p5 ∨ False)) ∧ ((p2 → p1) → True)) ∧ p3) ∧ ((p4 ∨ p2) → p4)))) ∨ (((p1 ∧ p3) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247528023998379976216394138536 : ((False ∨ p4) ∨ (((((p5 ∧ (True ∨ ((p4 ∧ p1) ∨ True))) → p4) ∧ (((p2 → p1) → p3) → (((p1 ∧ p5) ∧ p1) ∨ True))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111400479090985834081182124752 : (((p1 ∨ (p1 → (((False → p5) → (p3 ∧ (((p5 → ((p2 → ((p2 → p1) → p4)) ∧ p1)) ∨ p3) ∧ True))) ∧ False))) ∧ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229458956380128367602135208674 : ((p2 → (True ∧ False)) ∨ ((((((((p3 ∧ p4) → p2) → (((True ∨ (p1 ∨ False)) → p2) → False)) ∧ p2) ∨ p4) ∧ p5) ∨ True) ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166309570525515558992756058041 : ((p5 ∧ ((((((p2 ∧ (True ∧ True)) ∨ (p3 ∧ p4)) ∧ p4) ∨ True) → (p3 ∨ p1)) ∧ p1)) ∨ (p1 ∨ (((p2 ∨ (True ∨ p3)) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247576420236270534448304144710 : ((False ∨ p4) ∨ (p5 ∨ (((True ∧ p1) ∨ p3) → ((p4 → False) ∨ ((((False → (p2 → (p2 ∧ p2))) ∨ p4) ∨ (True ∨ p4)) ∧ (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748098143768394301504202068985 : ((((p1 → p2) → (p3 ∨ (((p3 ∧ False) ∨ (((p3 ∨ ((p3 ∨ False) ∨ True)) → (p5 → p5)) ∧ (p3 ∨ p2))) ∨ ((p1 → p1) ∧ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114538687090940404741643870129 : (((p2 → (p1 ∨ ((p2 → (((True ∧ (p3 ∧ p4)) → p4) → (p3 → (p3 ∧ p4)))) ∨ p3))) → ((p5 ∧ p1) ∨ (True → p2))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321104946051311331096750311791 : (p4 ∨ (p2 ∨ ((((((False ∨ (p5 ∨ p4)) ∧ (p4 → (p3 ∨ p2))) → (p2 ∧ ((p3 ∧ (p2 ∨ p2)) → p3))) ∧ p5) ∨ (p3 → True)) ∧ True))) := by
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
theorem thm_5_vars_178935623511284741914352382465 : (((False ∧ False) ∨ ((p5 ∨ (p1 ∨ (True ∨ p1))) ∧ (p3 ∨ (True ∨ p5)))) ∨ ((p3 ∨ ((p1 ∧ (p1 ∧ (True ∨ True))) → (True → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201259354678836532993769693799 : ((p3 → (((True → True) ∧ False) → (False ∨ p3))) → ((((p4 → (p4 ∨ p4)) → p1) ∧ (False → ((p4 ∨ p1) ∧ (p4 ∧ (False → p5))))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → (p4 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860110906416087608843231005461 : (((((((p3 → p2) → (p5 ∧ False)) ∨ ((True ∨ ((((False → ((True ∨ p5) → p1)) ∧ False) → p4) ∨ True)) ∨ p1)) ∨ (p1 → True)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → p2) → (p5 ∧ False)) ∨ ((True ∨ ((((False → ((True ∨ p5) → p1)) ∧ False) → p4) ∨ True)) ∨ p1)) ∨ (p1 → True)) := by
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
theorem thm_5_vars_241515776509864132631413046058 : ((False → p3) ∧ ((((((p4 ∨ p2) ∨ (p1 ∧ p5)) ∧ (p5 ∨ (True ∧ p5))) ∨ (p1 → (p5 ∧ ((p1 ∨ p1) ∧ (p5 → True))))) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184446222509285077096741035065 : (((p2 ∧ ((p4 ∧ p5) ∧ (True ∨ (True ∧ p5)))) ∧ (p5 ∧ p1)) ∨ (False → ((p5 → ((p1 → (((p2 ∧ p3) ∨ p5) ∨ p2)) ∨ p1)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165922664611458545989856525291 : (((p1 ∧ p5) ∧ (p3 ∨ (p2 ∨ (p5 → ((((False ∧ p2) → p3) ∨ (p2 ∨ p4)) ∧ True))))) ∨ ((p2 ∨ (p1 ∧ p1)) → (p1 ∨ (p3 → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_828060710131601017612393378701 : ((((p3 ∧ ((((p2 → p5) → ((p5 ∧ p5) ∨ (((p4 ∨ p2) ∧ (p5 → p5)) → True))) ∧ (p4 → False)) ∧ (p1 → (True ∧ p2)))) ∧ p4) → p2) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15001171260392017497191786139 : ((((p2 ∨ p4) ∨ (((p4 → False) ∨ ((p5 ∨ p1) ∧ ((((p3 ∧ p2) ∨ (p2 ∧ p5)) ∧ True) → p3))) ∨ (True ∧ True))) ∨ (p4 → False)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59589696267593366511963900705 : (((p4 → p1) ∨ ((p3 ∧ p2) ∨ (((p2 → (False ∧ ((p5 → p5) → (p1 ∧ ((p5 ∨ (p5 → (p4 ∧ True))) ∨ True))))) ∨ True) ∨ p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_149212085928371106463211671917 : (((False ∧ p3) ∨ (p2 ∨ (((p2 ∧ (p3 ∧ (True ∨ (((False → (p5 → p3)) → p1) ∧ p5)))) ∧ p3) ∧ p1))) ∨ (True → (p4 → (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156988136826830126656842349262 : ((((((p2 → p4) → p2) ∧ (p5 ∨ p2)) ∨ ((p1 → ((p1 ∧ p2) ∧ (False → True))) ∨ False)) ∨ True) ∨ ((p4 ∨ ((p2 ∨ p3) → p4)) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42909507132392136900707665581 : (((p3 → (p2 ∧ (((p4 ∨ p1) → ((p5 ∨ (False ∧ (p2 → (p4 ∧ p1)))) ∨ p5)) → ((((p4 → p4) ∨ True) ∧ p1) ∧ p4)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801382134688278532748415726698 : (((p2 → (((p4 ∨ ((((p1 → p4) → p5) ∨ p1) → (p3 ∨ p3))) ∨ p5) → ((((p1 → False) ∨ p5) ∧ (True ∨ (True ∨ True))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164826262345422424133741272502 : ((((False → True) → (((((p3 ∨ (p4 ∧ False)) ∨ p3) ∨ p5) → p5) ∨ (p3 ∧ True))) ∨ True) ∨ ((False → True) → (True ∨ (p4 → (p2 ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356153245993230302400256382986 : (p5 → (((p1 ∨ (p5 ∧ (((p2 → p5) ∧ p1) ∨ (p5 → (True → p2))))) ∨ (p2 ∨ (p1 ∨ p2))) ∨ (p5 ∨ (p5 → (p2 ∨ (p3 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725604484601230228110981488904 : (((((p3 ∧ p3) ∧ p3) ∨ (p5 → ((p1 ∧ ((((True ∨ ((p5 ∨ (True → p3)) ∨ False)) ∨ True) ∨ p5) ∨ (p2 ∧ p3))) → (False ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
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
            -- False on the left can always be used.
            apply False.elim h13
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
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123644512183781587990158857259 : (((((False ∧ ((p3 ∨ ((p5 → p2) ∨ p4)) ∧ True)) ∧ (p5 ∧ p2)) ∧ (p4 ∨ True)) → ((p5 → (p1 → (p2 ∨ p3))) ∧ p4)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202867955458736560381015920349 : (((False ∧ p2) ∨ ((p2 → True) ∨ p3)) ∧ (p1 → ((False ∨ (False ∨ (False ∧ p3))) ∨ ((p2 ∧ (p1 ∨ ((True → False) ∧ (p3 → p5)))) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712436318312096023548827795059 : (((((p4 ∨ (p4 ∧ p1)) ∧ (p2 ∨ p4)) ∨ (p5 → (p3 → (p2 ∨ (((p3 → ((p2 ∧ p3) ∧ p1)) ∨ ((p3 ∨ p3) → False)) → p3))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



