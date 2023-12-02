variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204103954920595751241244483409 : (((((p5 ∧ p5) ∧ p2) ∧ True) ∧ p3) ∨ (((p1 ∧ p5) → (False ∨ (((((p2 → p3) ∨ p1) → p2) ∨ (p5 ∨ p3)) ∨ (False ∧ True)))) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4272111887376614905897047360 : (True → ((((p5 ∨ (False → False)) → ((p2 ∨ ((p1 ∨ p4) ∧ (p4 ∨ ((p1 ∨ False) ∧ p2)))) ∨ (p4 → (p5 → True)))) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ (False → False)) → ((p2 ∨ ((p1 ∨ p4) ∧ (p4 ∨ ((p1 ∨ False) ∧ p2)))) ∨ (p4 → (p5 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h3
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218909064119160862262272205000 : ((p3 ∧ ((True ∧ False) → p4)) → ((p4 ∧ ((False ∨ ((True ∧ (p1 → (p3 → (True ∧ (p1 ∧ p4))))) ∨ ((p1 → p5) ∨ p2))) ∧ p2)) ∨ True)) := by
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
theorem thm_5_vars_301161253850242552494668434280 : (False ∨ ((p3 ∨ (((p4 ∧ (False → p5)) ∧ True) ∨ p1)) ∨ (((p3 ∧ (p1 ∨ p3)) ∨ (p3 → True)) ∨ ((((p2 ∧ False) ∧ p5) ∧ True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340100125029499166326025156041 : (p1 → (p3 → (((p2 → (p5 ∧ (((((((True → (p4 ∨ p2)) → True) → False) → p5) ∨ (p3 → p5)) → p3) ∧ True))) → False) ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311947550171499862391305212595 : (p2 ∨ (p3 ∨ (((p4 ∨ ((p1 → (p3 ∧ p5)) ∧ p4)) ∨ ((p1 → False) ∧ p3)) ∨ (p3 → (p1 ∨ ((False → p3) ∨ ((False ∧ p1) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113287444764554329511240228832 : (((((p5 ∨ ((((p3 → p1) ∧ p2) ∧ p3) → p5)) ∧ p5) ∨ ((False ∧ (False → True)) → ((p4 ∨ p3) ∧ p2))) ∧ (p4 ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346295792908388869006780364839 : (p3 → ((((p4 ∨ (True ∧ ((p3 ∨ False) ∧ (False → ((True ∨ p2) ∨ (p4 ∧ p5)))))) → (p1 ∨ (p2 ∧ (p5 ∧ False)))) ∨ True) ∨ (p3 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712052235580149431567264537838 : ((((((p5 ∧ p5) → (True ∧ p2)) ∨ p5) ∨ (((p2 ∨ p1) → ((p2 ∧ p5) ∨ ((False ∨ False) ∧ ((p4 → (p2 ∨ False)) ∨ p3)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310875594782946783433795612101 : (p2 ∨ ((False ∨ (p5 ∧ p3)) → ((p2 ∧ ((p4 ∧ (p3 ∨ (True → (p2 ∧ (((False ∧ p5) ∨ p5) → p4))))) → (p2 ∧ (p4 → False)))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82388174739003729162567915368 : ((((False ∧ ((p1 ∧ p4) → p5)) ∨ (((p3 ∨ (p5 → (((False ∨ p1) → True) ∧ p4))) ∨ True) → False)) ∧ (p5 → (p3 ∨ (p2 → p1)))) → p5) := by
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
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 ∨ (p5 → (((False ∨ p1) → True) ∧ p4))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263411205374212958008004159766 : (True ∧ (((p5 → p5) ∧ ((p3 → ((True ∧ (p1 ∧ False)) ∧ ((True ∨ (p1 → (p4 ∧ p3))) ∧ (False ∧ False)))) ∧ p4)) ∨ ((False ∨ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38784737828009332790077615819 : (((((p2 → p4) ∧ (True → p2)) ∨ ((((True ∧ (False ∧ (p4 ∧ (p5 → (((False → p3) → True) → p2))))) ∨ False) ∨ p2) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_553784414811581880283314057814 : (((p2 ∨ ((((p1 ∧ (((p2 ∧ p1) → (False ∧ True)) → (p2 ∧ p1))) ∧ True) → (p3 ∨ (p3 → False))) ∨ (p1 → (False → (p4 ∨ p5))))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111727399563203193197257876302 : (((((False → p2) ∧ (p3 → (p1 ∧ (p1 ∨ (p1 ∧ (True → (((p1 ∨ ((p1 ∨ p2) ∨ False)) ∨ p3) ∨ True))))))) → False) ∨ True) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133021941623213700175698423261 : ((p5 ∨ ((p3 → (p2 ∧ False)) ∨ (((p4 ∨ (False ∨ p4)) ∨ p3) ∨ ((p2 → True) → (((True ∧ p2) ∧ p2) → True))))) ∧ (True ∨ (p4 ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714230916567664073564100169692 : ((((((p3 ∧ p2) → p3) ∧ (True ∨ False)) → (((p1 → (((False ∧ (((p3 → p2) ∧ (p1 ∨ False)) ∧ p1)) ∨ p5) → True)) ∧ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727080230676596823293935316754 : (((((p5 → True) → p1) ∨ (p3 ∨ (False ∨ (True ∧ ((True ∨ ((((p2 → p4) ∨ (p1 → p1)) ∨ (p2 ∧ (p2 ∨ p2))) ∧ p5)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656213167075996882594998276752 : (((((((p1 → True) → (((p4 → p2) ∨ (p4 ∧ p2)) ∧ p3)) ∨ (p2 ∨ p1)) → (p2 → (p4 ∧ (False → (p3 ∨ p4))))) ∨ (True ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299350496103785126427556274810 : (False ∨ ((((p4 ∨ p2) ∨ True) → (((p3 ∨ p3) ∨ (((False ∧ True) ∧ p1) ∧ ((True ∧ (p4 ∨ True)) → ((p3 ∧ p5) ∨ True)))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678261584665686070958153015883 : ((((((False ∧ (p2 → ((p5 → p4) → p1))) → p2) ∧ ((p3 ∧ p3) ∧ ((p4 ∨ (p1 ∧ True)) ∧ p5))) ∨ ((p5 → (p1 ∨ False)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8289938594232750880536172082 : ((((((p5 → ((True → (p1 ∧ (p4 ∧ ((False ∨ False) ∧ ((p3 ∨ p3) ∨ p5))))) ∨ (p3 → True))) ∨ False) ∧ (p3 → p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75722399717554730432778861988 : (((((((((p5 → (p4 → True)) ∨ p2) → p3) → True) → ((((False ∧ True) ∨ (True → p5)) ∧ True) ∨ False)) ∨ (p1 ∧ p1)) ∨ True) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p5 → (p4 → True)) ∨ p2) → p3) → True) → ((((False ∧ True) ∨ (True → p5)) ∧ True) ∨ False)) ∨ (p1 ∧ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148385942273384862076120793196 : (((((False ∨ True) → (p1 ∨ p5)) → (p5 ∨ (p1 ∧ ((False → p5) ∨ p4)))) ∨ ((p3 ∨ p4) → (p5 ∨ p1))) ∨ ((p5 ∧ (p3 → False)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638522864060492139678405291416 : ((((((p3 ∧ (p5 ∨ True)) ∨ (p3 ∧ p5)) ∨ (p4 → (p4 ∨ ((p4 ∨ True) ∧ ((((p2 → p5) ∧ (p2 ∧ p1)) ∨ p5) ∧ p3))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303126604264984208962420421239 : (False ∨ (p3 → (((False ∧ (p2 → True)) ∧ (False ∧ (p5 ∧ (p1 → (False ∧ p4))))) ∨ (False → (p1 ∨ ((p5 ∨ (p3 ∧ (p4 → p4))) → p5)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177917728543563681773313722503 : (((((True ∧ ((p5 → True) → False)) ∨ p2) ∨ ((p2 ∨ p5) → False)) ∨ True) ∨ (((True ∨ (p4 ∧ True)) → p3) ∨ (((p4 → True) → False) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193923641078182826394267404798 : ((p1 ∨ (p1 ∧ ((p4 → True) ∧ (False → (p3 ∧ p1))))) → ((p2 ∧ p3) ∨ ((p5 → (p4 → (p5 ∨ p5))) → ((p1 ∨ (p5 ∨ True)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66043728736903651596975869974 : ((p5 ∨ ((p2 → (((((p3 ∨ p1) ∧ p3) ∧ (p4 → False)) → (False ∧ (p5 → ((((p5 → p4) ∧ p5) → False) ∧ p5)))) ∨ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174059698694909676237012096340 : (((p4 → (((((p3 → p2) ∧ p1) ∧ p1) → (p5 ∧ False)) ∨ (True ∨ False))) → p2) → ((p4 ∧ ((p5 ∧ p5) ∨ p5)) ∨ (p5 → (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (((((p3 → p2) ∧ p1) ∧ p1) → (p5 ∧ False)) ∨ (True ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160754398642850194872356269148 : ((((((p5 ∧ p4) ∧ True) → p3) ∧ p3) ∧ (((True ∨ p4) ∨ p2) → (False → (p4 ∧ (p1 ∧ p5))))) → ((((p5 → p4) ∧ True) ∧ p5) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356642043868425898200423709038 : (p5 → ((p4 → ((True ∨ ((True → True) ∨ p1)) → p3)) ∨ ((((((False ∧ p2) ∧ True) ∨ p2) ∨ (p1 ∨ (p1 ∨ False))) ∨ (p5 ∨ p4)) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111946478016495951186125858326 : ((((((p2 → (False ∨ p4)) ∧ (p3 ∨ p4)) ∨ True) ∧ (p3 ∨ ((False ∧ ((p5 → (False ∧ True)) → p4)) → (p2 → False)))) ∨ p2) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252128493327900903817836258030 : ((p4 → p2) ∨ (p2 ∨ ((True ∧ ((True ∧ (False ∨ True)) ∧ (((p1 ∨ ((p5 ∨ p4) → False)) → (p3 → (p2 ∧ p1))) ∧ p2))) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_38048166139314381941256562665 : (((((p1 → (((p3 → (((p4 → p2) ∨ (p1 ∧ (p1 ∨ True))) → True)) ∧ False) ∨ ((False ∨ p2) → False))) → p2) → (p4 ∧ p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723890672223489413223116187995 : ((((True ∧ (True ∨ False)) ∧ (((p1 → ((False ∧ (p3 ∧ p5)) ∧ p5)) → (p2 → False)) → (p3 ∨ ((True → (p2 ∨ (p1 ∨ True))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183794167828895796239799354674 : ((((((True → True) → (False ∨ (p1 ∨ True))) ∨ p1) ∨ p2) ∧ p3) ∨ ((p1 ∨ False) → ((p1 → ((p1 ∧ True) ∧ p3)) ∨ (p2 → (p3 ∨ p1))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696991781111358547522963773287 : ((((((p3 → ((p3 ∨ True) ∨ False)) → False) ∧ ((p2 ∧ p5) → p3)) ∧ ((p5 ∨ (p4 → p3)) → (((p1 ∨ False) ∧ (p2 ∧ False)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114424689441263489153898100907 : (((False ∧ (p4 ∨ (((p2 → (True → (p1 ∨ (False ∧ (False ∧ (True ∨ p5)))))) ∧ False) ∨ p4))) ∨ (False → (p3 ∧ (False ∧ p4)))) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325763085808513485341857908528 : (p5 ∨ (p2 ∨ (((False ∨ False) → p5) ∧ (p2 ∨ ((((False ∧ (p2 ∨ False)) ∧ p2) ∨ (p3 → p2)) ∨ ((p2 ∧ False) ∨ (False → (p2 ∧ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38286734874816228777985994951 : (((((p2 ∨ p1) ∨ (p2 → (False ∧ ((p3 ∧ (False ∧ (((p5 ∨ p4) → p2) ∧ True))) ∨ True)))) ∨ (p3 → (False → (p4 ∨ p2)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233298916895566983202619003447 : ((True ∨ (p3 ∨ True)) → (((True ∨ p3) → (p3 → ((p2 → False) ∨ p1))) ∨ ((((False ∨ (p3 ∨ (p4 ∧ True))) ∧ p2) ∧ p3) → (p2 ∨ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357488878239565759154484664389 : (p5 → (True ∧ (((p5 ∧ (((p3 → (True → p4)) ∧ p2) → False)) ∨ (((p3 ∨ (True ∨ p3)) → (p1 → (p5 ∨ (p2 → p1)))) → False)) ∨ True))) := by
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
theorem thm_5_vars_59971430674420498234665150774 : (((False ∨ True) → (((p5 ∧ p2) → (False ∧ (p5 ∨ p1))) → (((((p1 ∧ p5) ∧ ((True ∧ (p2 ∧ p4)) ∧ p5)) → p3) ∨ p2) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81885238111022644084607532917 : ((((((p4 ∨ ((p2 → p3) ∨ p1)) ∨ ((((p5 → True) → (p4 ∨ p5)) ∨ p1) ∨ p2)) ∨ True) ∨ (p5 ∨ p2)) → ((p2 ∧ p1) ∧ p2)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ ((p2 → p3) ∨ p1)) ∨ ((((p5 → True) → (p4 ∨ p5)) ∨ p1) ∨ p2)) ∨ True) ∨ (p5 ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586278404437114657694259987195 : ((((((((p3 ∧ (p2 → p3)) ∧ p5) → (True ∧ p2)) ∧ ((((p5 ∧ ((False → p3) ∧ (p5 ∨ p3))) → p3) ∨ p4) ∧ True)) ∧ p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318652517456481916805040657053 : (p4 ∨ ((p1 → ((((((p2 ∨ p4) ∧ (p4 ∧ p5)) ∨ (p4 → False)) ∧ p3) ∧ p2) ∧ (((True → (p5 ∧ True)) ∨ True) → p3))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37518959032231842657513449414 : (((((p3 → p2) → (((True → (True ∧ (((p3 ∧ ((p1 ∧ p2) ∨ (p2 ∧ p3))) → (p2 ∧ p3)) → p5))) → p4) → p2)) ∨ p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677457066848850211370727898303 : (((((((p1 ∧ False) ∨ (p3 → (p1 → (p2 ∨ (p4 ∧ p3))))) ∧ ((p1 ∧ False) ∧ (p2 ∨ p5))) ∨ True) ∨ ((True → (p1 → p3)) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_256743890595173355093314125828 : ((p1 ∨ p1) → (p2 ∨ (((p1 ∨ p4) → ((p5 ∧ (False ∨ ((p2 ∧ ((p5 ∨ p2) ∧ (p5 ∨ True))) ∨ (p3 → p2)))) ∧ (True ∧ p2))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308778247165474368027680817977 : (p2 ∨ ((((True → False) ∧ (p3 ∧ (((True ∨ ((p4 ∧ p2) ∧ (((True ∨ p4) → (p3 ∧ True)) → p1))) ∧ True) ∨ (True → p2)))) ∧ p1) → p2)) := by
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
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790116668246220104310753937502 : (((p5 ∨ ((p1 ∨ p5) → (((p4 → ((p1 ∨ ((False ∨ p2) ∨ p1)) → (True ∨ p4))) → p1) ∧ (((True → p5) ∧ p1) ∨ (p3 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48103206116999146071805819868 : ((((((p1 ∨ True) ∧ p3) → p5) ∨ ((((p2 ∨ (p3 ∧ (((p5 ∨ p4) ∨ p5) → True))) ∨ p2) ∨ p4) ∧ (p2 ∧ p1))) → (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330914693446745464392008404122 : (True → (p4 → (((((p2 → (p2 → ((True ∧ p5) ∨ p3))) ∧ True) → ((True → (p3 ∨ (True ∧ (p3 ∨ p4)))) ∧ p3)) → p2) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_115363757974966806750195449067 : ((((((p3 → p1) ∧ (False → False)) ∧ p3) → p2) ∧ ((((False → p2) → p1) ∨ (p3 ∧ (True ∧ (False ∨ (True → p5))))) ∨ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141873065452199976712046484287 : (((False → True) ∨ (p5 ∨ ((((p2 ∨ p5) ∧ p2) ∧ (p1 → (True ∧ p5))) → (p3 ∧ (p4 ∧ (p5 ∧ (p1 ∨ p5))))))) → (p3 → (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116028443570662484793646839741 : (((p4 ∧ ((True ∨ p2) ∨ p5)) → (((p5 ∧ (p2 → p5)) ∧ (p3 ∨ ((False → (p1 ∧ False)) → p4))) → ((p2 ∨ p4) → p1))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111892525477490048255691337097 : (((((p2 ∨ (True ∧ (p5 ∨ (p1 ∧ (p4 ∨ (p4 ∨ (p1 ∧ p5))))))) ∨ False) ∨ (p4 → (((False → p1) ∨ p4) ∨ p1))) ∨ p5) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727742269272185793436196302455 : ((((False ∨ (p4 ∧ p3)) ∨ ((((p5 → (p4 → p1)) ∨ False) ∨ ((p1 ∨ (p1 ∧ (((True ∧ p5) ∨ True) → False))) ∨ p4)) ∨ (False → False))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49335827618842671936778644964 : (((True → ((((((p4 ∧ ((p1 ∨ (p3 ∨ p2)) → p4)) ∧ ((p1 → True) ∨ p1)) ∨ p5) → p2) ∨ p3) ∨ p4)) ∨ (p1 → (p2 ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_166199556994846119188928291752 : ((p1 ∧ ((p5 → p2) ∧ (p5 ∨ (((p3 ∧ p2) → ((p1 ∧ p3) ∧ p5)) ∨ (p4 → p1))))) ∨ ((p3 ∧ (p2 → (True ∨ True))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89167652718249290541482689914 : ((((p3 ∨ True) → False) ∧ ((p5 ∧ (((p3 ∨ p5) ∨ ((((p2 ∨ False) ∧ p4) → p2) ∧ p1)) ∧ (p4 ∧ p4))) ∨ (p5 → (p4 ∨ p3)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p3 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h8.left
        let h17 := h8.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h8.left
      let h24 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h28 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h29 := h2 h28
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217817767442470576691752319440 : (((p2 ∨ (p5 → p5)) → False) → (False ∧ (((False ∨ p2) ∨ p5) ∨ (p1 ∨ (((True → p4) ∨ ((p5 ∧ True) ∨ (p2 ∧ (p3 → p5)))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165472254976238400873006056758 : (((p2 → (False ∧ (((p1 ∧ False) → (True ∨ p4)) ∨ p2))) ∧ (p5 ∧ ((p3 ∨ False) ∧ True))) ∨ (p2 → (p2 → ((p1 ∨ p2) ∨ (p4 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18581095653217550265539325039 : ((((((p2 ∨ (p5 ∧ p4)) → (p1 ∨ p4)) → (p1 ∧ p3)) → ((p2 → p3) → (p2 → p3))) ∧ ((p4 ∧ p5) ∨ (p3 → (False → p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165334403563459845191549812380 : ((((p3 ∨ (((p1 ∧ (p3 ∧ p2)) ∧ (True ∨ p5)) → True)) → p2) ∧ (True ∧ (p5 ∧ False))) ∨ (p3 → (p3 ∧ ((p4 ∧ p3) → (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42238024609421706638291828728 : (((False ∧ ((p2 ∨ p3) → (p3 ∧ ((True ∧ p1) → ((((p3 ∨ p2) → ((True → (p1 → (p5 ∧ p2))) ∨ p5)) ∨ p4) ∧ p3))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47446045689457985641949377814 : (((p3 ∧ ((True ∧ p3) ∧ ((((p3 → (p3 ∨ (p5 ∨ (False ∨ p1)))) ∨ p5) → p2) → ((p3 ∧ (p1 ∨ p3)) ∨ p2)))) ∨ (True ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318595645662393301988444318583 : (p4 ∨ ((((True → ((p5 ∨ (((p3 → p4) ∧ p1) → p4)) → (p1 → p1))) → False) → ((p5 → False) ∧ (p4 ∨ (False ∨ p3)))) ∨ (p4 ∧ True))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → ((p5 ∨ (((p3 → p4) ∧ p1) → p4)) → (p1 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (True → ((p5 ∨ (((p3 → p4) ∧ p1) → p4)) → (p1 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h10
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150354756324073183804726082603 : ((p5 → (((p3 ∧ p2) ∨ True) → ((((p5 ∧ ((p5 ∨ p1) → p1)) ∨ (p2 → p3)) ∧ p5) → (p5 → p3)))) ∨ (p1 → (True ∨ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324280356083992900378801957232 : (p5 ∨ ((p3 → ((p1 → p3) → ((p4 ∧ p5) ∨ p2))) ∨ (p3 ∨ (((p3 → False) ∨ (((False ∨ (False → p5)) ∧ False) → True)) → (True ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87764808498411227448064345121 : (((((False → (True ∨ p3)) ∧ p2) ∨ True) → ((((p1 ∧ False) ∨ ((p5 ∨ (True ∨ ((True → p1) ∨ p5))) ∨ p5)) ∧ True) ∧ (True ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (True ∨ p3)) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113098558343511721311160193674 : (((True → ((((p4 ∧ p2) ∨ ((((((p2 ∨ (True ∧ True)) ∧ (p1 ∧ True)) → p2) → p4) ∨ p2) ∨ p4)) ∧ p2) ∧ p2)) → p2) ∨ (p2 ∨ p1)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326853223455290154935701838484 : (True → (((p2 ∨ ((False ∧ ((p3 → (p1 ∧ (((False ∨ p1) ∨ False) ∧ p4))) ∧ p3)) ∧ (False ∨ (((p4 ∧ False) ∨ False) ∨ p4)))) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133643492004547114308769438497 : (((((((p4 ∨ (p1 → p5)) ∨ (p2 ∨ (p4 → (p5 → (True → (p4 ∧ p1)))))) → p3) → False) ∧ (p4 → p2)) ∧ False) ∨ ((p3 ∧ p2) → p3)) := by
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
theorem thm_5_vars_158546962015313326301094282227 : (((p4 → True) → (p1 ∨ ((p4 ∧ ((p4 → p5) ∨ True)) ∨ (((p5 → p3) → p2) ∨ (True → p2))))) ∨ (((p4 ∧ p2) ∨ True) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158204101576072226333864484901 : ((((p2 ∨ p4) ∨ False) ∧ ((True ∨ (((False ∨ (p3 → p4)) ∧ ((p5 ∧ p4) → p2)) → p5)) → p3)) ∨ (False → ((p1 → False) → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188130262605170163235773032293 : (((((p2 ∨ p2) ∨ ((p4 ∧ p4) ∨ p5)) ∨ p2) ∨ True) ∧ ((((p3 ∨ (True → ((p5 ∨ p2) ∧ ((p1 → p1) → False)))) ∨ False) → p3) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h8
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249909507072213399056606849122 : ((True → p1) ∨ (((p4 ∧ (p2 ∨ p2)) → (p2 → (((False ∨ p1) ∧ (p5 → ((False ∨ p4) ∨ ((p1 → p4) ∨ p2)))) → False))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322248189485662969836318960043 : (p5 ∨ ((((((p4 ∧ (p3 → ((p1 → ((False ∨ (p3 ∨ p5)) ∨ False)) ∨ p2))) ∧ p4) → (p5 ∨ (False ∧ p1))) ∨ (p5 → p2)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345327548002694500896997689226 : (p3 → ((((((p4 ∧ (((p2 ∨ ((p3 ∨ p3) → False)) ∨ p2) ∨ (p1 → p5))) ∧ p3) ∨ p4) ∧ (p3 → (p2 → (True → p2)))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186997978498465987951367945043 : ((((p5 ∧ p2) ∨ False) → ((((True → p4) → p3) ∨ p4) ∨ p4)) → (((p3 → (((False ∨ ((False → p1) ∨ p4)) ∧ True) ∧ p5)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40928407290350029020648526379 : ((((((((p3 → p2) ∨ True) → ((p2 ∧ (p1 ∨ True)) ∨ (True ∨ (p3 → p1)))) → ((p3 ∧ False) ∧ p4)) ∧ p4) ∨ (p2 → True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697320766530659717144001187066 : (((((p2 ∨ True) ∨ (p1 ∧ (p2 → (((p1 ∨ p1) ∧ p3) ∨ p4)))) ∧ (p5 ∨ (((True → (p1 ∨ p5)) ∧ ((p5 ∧ p1) → p5)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111140158789976133162955107474 : ((((((p4 ∨ True) ∧ (p4 ∧ p4)) ∨ p1) ∧ ((p5 ∨ (p5 ∨ (p2 ∧ p3))) ∨ (((p3 → (p1 ∧ p3)) ∨ p5) ∧ p2))) ∧ True) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197113791741164528507631510828 : (((False ∨ (p1 ∨ ((p4 ∨ p1) ∧ p1))) ∨ True) ∨ ((False → ((p5 → (p2 → (p4 ∨ ((False ∨ True) ∧ (p4 → p5))))) → (p5 → p2))) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219762029681528346176566308279 : ((p2 → ((False ∨ p2) ∨ p1)) → (True → (p1 → (p1 → ((((p1 ∨ p2) → (p1 ∧ False)) ∨ ((((False ∧ False) ∧ p5) ∧ p1) → p1)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119390397955681349875000896472 : ((p4 → (((((p1 ∧ p3) ∨ ((p1 ∨ (False → p5)) → ((p2 ∨ ((False → p2) ∧ p5)) ∧ p1))) ∨ p2) ∨ (p4 → p4)) ∧ True)) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191429669953920918431689835030 : (((p2 ∨ p4) → (p1 → (((p5 ∨ p2) ∧ False) ∨ p1))) ∨ ((True → ((p1 ∨ True) ∨ ((p1 ∨ (p2 → ((p5 ∨ p2) ∨ True))) ∧ p4))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324024214648088405981721160227 : (p5 ∨ (((p2 ∧ (p4 → (p4 ∧ p5))) ∧ ((p1 ∨ (p1 → p2)) → (True → p5))) → (False ∨ ((p1 → ((p5 ∨ (True ∨ p1)) → p1)) ∧ p5)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ (p1 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41025017640130582265207849463 : (((((((p2 ∨ p3) → (p1 → (((((p5 → p5) → p3) ∧ True) ∧ False) ∧ False))) ∧ (p5 ∧ p2)) ∧ (p3 ∨ p3)) → (True ∧ p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134338296679543839802268223087 : (((p4 ∧ (((p2 → (((p5 ∨ p4) ∧ p5) → p5)) → ((p5 ∧ True) → (p2 ∧ (p3 ∨ p2)))) → (p3 ∧ p2))) ∨ True) ∨ (p3 → (p2 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635545967023646774017296982538 : ((((((p3 ∨ (p2 ∧ (((p1 ∧ (p4 ∨ p3)) ∨ (p2 → (p3 → p2))) ∨ (False ∨ True)))) → p3) ∨ ((p1 ∨ p3) ∧ (p4 → p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109508012681849105494859288505 : ((p2 ∨ (p1 → ((((p3 ∨ False) ∨ p4) ∧ p5) ∨ (True ∨ (((p5 ∨ (True → ((p4 → (False ∧ p1)) ∨ p5))) ∨ True) ∧ False))))) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729957467777588956479397919382 : (((((p4 ∧ p5) → p3) → ((True ∧ ((p3 ∧ (p2 ∨ (((p2 → ((p5 → p4) ∧ (p3 ∨ p3))) ∧ p2) ∨ (p1 ∧ p5)))) ∧ p4)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345385903411558063829470584266 : (p3 → (((p4 ∨ ((p5 ∨ (p2 → False)) ∧ ((((p5 ∧ ((True → ((True ∨ p5) ∨ False)) → (False → p5))) ∨ p1) → p5) ∨ False))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310503316383154477595104655050 : (p2 ∨ (((p5 ∧ p4) ∨ (p5 ∨ (p2 ∨ False))) ∨ (((p4 ∧ ((p5 ∨ (p2 → (p5 ∧ p3))) ∨ False)) ∧ (((True ∧ p1) → p4) ∨ p2)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755837433586008314376004975407 : (((p1 ∧ (((((p2 → (((False ∨ True) ∧ ((False ∧ p2) → p4)) → p4)) ∧ p4) ∧ ((p4 ∧ p3) → ((p1 ∨ p2) ∧ p3))) ∧ p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137693777427452191730086564094 : ((p1 ∨ ((p2 ∨ ((((((((True ∧ p1) → (p5 → (p5 → False))) → p5) ∧ p1) ∨ True) → p4) ∧ p5) ∧ p5)) → p1)) ∨ ((True ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62801728570561009905291219643 : ((p4 ∧ (((p5 ∨ p5) → (p1 ∧ (True → ((p5 ∧ (p4 → (p1 ∨ False))) → p2)))) ∧ ((p3 ∧ (p3 ∨ True)) ∧ ((p4 ∨ p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



