variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703837797675429932693030848492 : ((((((((True → p1) ∧ p2) ∨ (False ∧ False)) → p4) ∨ True) → (((p2 ∧ (p2 ∧ p2)) ∨ ((True ∧ ((p1 ∨ p5) → p3)) ∧ False)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714550036512778315917704733047 : (((((True ∧ p3) ∨ ((p5 → p1) ∧ True)) → (p5 ∨ (True → ((((p5 ∨ (p2 ∧ p1)) ∨ p3) ∧ p1) ∨ (p1 ∨ ((True → p5) → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146938053994773530199766050399 : ((((((((((((p4 ∧ True) ∨ p5) ∧ p4) ∧ (p3 → p1)) ∧ p3) → p3) ∨ p1) ∧ p2) → False) ∨ True) ∧ p1) ∨ (True ∨ ((p4 ∧ p3) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149581720639159873784686138592 : ((p3 ∧ ((p2 ∧ (p4 ∨ (p4 → ((((((p3 ∨ (p4 ∨ p5)) → p3) ∧ True) → False) → p3) ∨ False)))) ∧ p3)) ∨ (p2 → (True ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233441118314919268683847197529 : ((False ∨ (False → p1)) → (((p2 → (False ∧ (p3 ∧ p2))) ∧ p4) ∨ ((True ∧ ((False ∧ p4) ∨ False)) ∨ (True ∨ (((False → False) → p3) ∧ p3))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405494397762201737504486935194 : (((((((p2 → p3) → p2) → (((((p2 ∨ (p1 ∨ p5)) → True) ∧ p2) → ((p4 ∧ p3) ∨ p4)) ∨ ((False ∨ p3) → p3))) → False) → p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p3) → p2) → (((((p2 ∨ (p1 ∨ p5)) → True) ∧ p2) → ((p4 ∧ p3) ∨ p4)) ∨ ((False ∨ p3) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303241588043077735829337382954 : (False ∨ (p5 → ((p4 ∨ (((p1 → (((((False ∨ ((True ∨ True) ∨ True)) ∧ False) ∨ True) ∧ True) ∧ p4)) ∨ p3) ∧ p3)) ∨ (False ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737610079674110273100862722267 : ((((p5 → p2) ∧ (((((False ∨ ((False ∧ False) ∨ (p3 ∨ p2))) → False) ∨ (p1 → p1)) → (p1 ∧ p5)) ∨ ((p2 ∨ False) ∧ (False ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61808377951879052174853707570 : ((p2 ∧ (((((True ∨ True) ∧ p4) ∧ (p1 ∧ ((True → (p4 ∧ (((p4 ∧ False) → p2) ∧ (p1 ∨ p3)))) ∧ p1))) → (True ∧ p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782913203241178974944993551440 : (((p3 ∨ ((((((p3 ∨ True) → p5) → p4) → (p5 ∧ (((p5 → p4) ∧ (p2 → True)) → p4))) ∨ (p3 ∨ (p2 ∧ p1))) ∧ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639701648698606801398258185872 : (((((p5 ∨ (p1 ∧ p1)) ∧ ((((False → p3) ∧ (p4 ∧ True)) → p1) ∧ ((((False ∧ (p4 → False)) → (p3 ∨ True)) ∨ False) ∨ p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250007985543273677404382695075 : ((True → p2) ∨ (p1 → (((p3 ∧ (p4 ∨ p1)) → p2) → (((p1 → (((False ∧ p2) ∨ p4) ∨ (p2 ∧ ((p4 ∨ p3) ∨ p1)))) ∨ p1) ∨ False)))) := by
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
theorem thm_5_vars_431872144215504082419161498113 : ((((False ∨ (True ∧ (p2 ∨ ((True ∨ False) → ((((p3 ∧ p5) ∨ p3) ∧ (p4 ∧ False)) ∨ ((True ∨ (p1 → True)) ∨ p3)))))) ∨ (p4 ∧ p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54842542228994653512583127028 : (((p5 → (((p5 → p3) → (True → False)) ∨ p2)) → (p5 ∨ (((p2 ∧ (p5 ∧ (p2 ∧ True))) → ((False ∧ p2) ∨ p3)) → (p4 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654994726228312500313923427718 : ((((((p4 ∨ p4) ∧ ((((False → p3) → False) → (p5 ∨ p2)) ∧ (True ∧ (p1 → ((p2 → p5) ∧ (p3 ∧ False)))))) → False) ∨ (False → False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_119163148120638913897303543604 : ((p2 → ((((False ∨ (((((p3 ∧ p4) ∨ False) ∨ (True ∨ False)) ∧ p4) ∨ ((p4 ∨ True) ∨ p2))) ∧ (p2 ∨ True)) ∨ p5) ∨ p4)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322585581411634836090265653449 : (p5 ∨ ((True → ((p3 ∧ (p1 ∧ p1)) ∨ ((p1 ∧ ((p5 → False) ∧ ((((False ∨ True) ∨ p2) ∧ p5) ∧ ((False ∨ False) ∧ p5)))) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593579994873885754070707418971 : (((((True → (((p3 ∧ ((p1 ∨ p4) → False)) ∧ p2) ∧ ((((p4 ∧ (p1 ∨ True)) → p4) ∨ False) → True))) → ((True → p3) ∧ p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136139147060507244952723706468 : (((((True ∧ (True ∨ p4)) → (False ∨ p3)) → p3) → ((((p4 ∧ (p5 → p2)) ∨ p4) → (p2 ∨ p3)) → (p3 → False))) ∨ ((p5 → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148508895721430008591057989906 : (((p2 → ((((True ∨ p5) → p4) → (p5 ∨ (p1 ∨ p1))) ∨ True)) ∨ (True ∨ (((True → p2) ∨ True) ∨ False))) ∨ (p3 → (p2 → (False ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638963063143777566755288990521 : (((((True ∨ (True → (False → p3))) ∧ ((((p4 ∨ ((p3 ∧ (True ∨ p2)) → ((p1 ∨ p4) ∨ p2))) ∨ p3) ∧ (p2 → True)) ∨ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314545568647575610895854872641 : (p3 ∨ (((((False ∧ p2) ∨ ((p4 ∧ p1) ∧ p4)) ∨ ((True ∧ True) → p5)) ∨ (p1 ∧ (False ∧ True))) ∨ (True ∨ ((p2 → (p4 → True)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124225793801716663733650507748 : ((((p2 → (True → (p3 ∧ ((p3 ∧ p3) → p4)))) ∨ p5) → ((((p1 → p5) ∨ p3) ∧ (p1 → p1)) ∨ ((p3 ∨ True) ∧ True))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149537327068851232170192083622 : ((p2 ∧ (((p4 → (((p2 ∧ p3) → (p1 ∨ (p5 → (p4 ∧ ((False → p4) ∨ p1))))) → p3)) → p1) ∨ p2)) ∨ (True ∨ ((True ∨ p2) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112863299971929477661462590764 : ((((p2 ∨ (p1 → p4)) ∨ (((True ∧ ((True ∨ (p4 ∧ True)) → True)) → ((p4 ∨ p5) → (p1 ∧ (p5 ∧ p1)))) ∨ p3)) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157981194461855238359789225702 : ((((False ∨ (((p3 ∧ p3) → False) → p5)) ∧ p4) → (((p1 → (p2 → (True ∨ p3))) → p5) ∧ p1)) ∨ (p3 ∨ (p5 → (p5 ∨ (p3 ∨ p1))))) := by
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
theorem thm_5_vars_649917966467586738429370944305 : (((((False ∧ (p2 ∨ ((p3 → (True ∧ (True ∧ (((p5 ∨ (p3 ∧ True)) → p3) → p2)))) ∨ p2))) ∧ (True ∨ (p1 ∨ p2))) ∧ (True ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204250209667688696383246933580 : ((((p2 → False) ∧ (p3 ∧ p3)) ∧ p4) ∨ ((p4 → ((((p1 → ((p5 ∨ p5) ∧ p5)) → (p1 ∧ p5)) ∧ False) ∨ True)) ∨ ((p3 → p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736773894658765535730118261133 : ((((p2 → p2) ∧ ((p4 ∨ ((((p5 ∧ (p5 ∨ False)) ∧ p4) → (True → ((p1 ∨ p1) → ((p1 ∨ (p1 → p5)) → p3)))) → p4)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606209360586764121760424859077 : ((((((((p5 → p1) ∧ (True → (p3 ∨ (p1 → False)))) → (p3 ∧ (p1 ∨ (((False ∧ p2) ∧ p1) ∧ (p3 ∨ p4))))) ∧ p2) ∧ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318586948707113774599311625276 : (p4 ∨ ((((p2 → p5) ∧ (False ∨ (p1 ∧ (((p2 ∧ p3) ∧ ((p1 ∧ p2) ∧ p3)) ∨ (p3 ∨ p5))))) ∨ (p1 ∨ (p3 → False))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185288337973839045816932287094 : ((p2 ∧ (((False ∧ (p5 ∧ True)) ∧ True) ∧ ((p5 ∨ p3) ∧ p4))) ∨ ((p2 → (p3 ∨ ((True → p3) → ((False ∧ p3) ∨ (p2 ∨ p1))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219930375986807095968864992089 : ((p4 → (p3 ∨ (False → p4))) → (((False → True) ∧ (False ∨ (p2 ∨ (p2 → (p1 → p5))))) → ((((p2 ∨ False) ∧ (p1 ∨ p3)) ∨ True) ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307701454499421979246338028731 : (p1 ∨ (p2 → ((p5 → p4) ∨ (True ∧ (((False → p2) ∧ ((((p5 ∧ p4) → (p5 → (p4 → p3))) → p5) ∧ ((p4 ∧ p2) ∨ p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_307510711425106841347801411607 : (p1 ∨ (True → ((((False ∧ p2) ∨ True) ∧ (p4 ∧ p1)) ∨ (((((p2 ∧ ((p2 ∧ True) ∨ True)) ∨ ((p3 ∧ p1) ∨ p5)) ∧ p1) → p1) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47157122645391808061739792222 : (((((p3 → ((p1 ∨ True) → p2)) → (p3 ∨ (False ∧ ((False → (p2 ∨ p5)) ∨ p2)))) → (((p2 → p4) ∧ False) ∨ p5)) ∨ (False ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343152889120179856372330318456 : (p2 → (((p3 ∨ p4) → p4) ∨ (((False ∧ (True ∨ p3)) ∨ (p2 → ((((((p1 ∨ p3) ∧ p5) ∧ p2) ∨ (p2 ∧ p2)) ∧ True) ∨ False))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147422170875907605627947190466 : ((((True ∨ (True → False)) ∧ (((False ∨ p4) ∧ ((True → False) ∧ ((False → True) ∧ False))) ∧ (True ∨ True))) ∨ p1) ∨ (p2 ∨ ((True ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304044134535561319220871877068 : (p1 ∨ ((p4 ∧ (p2 ∨ (((p4 ∨ True) → ((p2 ∧ False) ∧ (p2 → (True → True)))) ∨ (p5 ∧ (((p4 ∨ (p5 ∨ False)) ∧ p5) ∧ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258964062024707430268331472683 : ((True → p3) → (((False ∧ (False → p1)) ∧ (p3 ∧ (((p1 ∧ ((p4 → p2) → p4)) ∨ (True ∨ p4)) ∨ p3))) ∨ ((p5 → p2) → (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68321562660770895649372631908 : ((p3 → ((p4 ∧ (p1 ∨ (((p2 → p5) ∨ (p2 → True)) → (((True ∨ p5) ∧ p2) → True)))) ∨ (p1 ∧ ((True → (False ∧ p1)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242997817723332747142786282781 : ((p4 → True) ∧ (((((p5 ∨ (p1 → True)) ∧ True) ∨ False) ∧ (p4 → False)) ∨ (((p3 ∨ p4) → p1) ∨ (False ∨ ((False ∨ (p4 ∧ p4)) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805402933587563303004455343985 : (((p3 → (p1 ∨ ((((p4 ∨ (p3 → (p4 ∧ (p2 ∨ p4)))) ∨ (p1 ∨ p2)) ∧ (p3 ∨ (p2 → ((p4 ∧ p2) → True)))) ∨ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668944425012359994929687249112 : (((((p3 ∨ ((((p4 ∧ (p1 ∨ (((False ∧ p5) ∧ (p3 ∧ p3)) ∧ p2))) ∨ (True ∧ True)) ∨ p2) → p3)) ∨ p4) ∨ ((p5 ∧ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190874926927760987111682068675 : ((((False ∧ (p3 ∧ True)) → (p5 → p4)) → (p2 ∨ p2)) ∨ ((((p4 → p2) → p1) → (p1 ∨ p2)) ∨ ((p3 ∧ (p2 ∧ (False → p5))) → p3))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310767461784654298842882871925 : (p2 ∨ (((True ∨ p5) ∧ p1) ∨ ((p2 ∨ (((((p1 → p4) → ((p2 → p5) → p4)) ∨ False) → (p4 ∨ p3)) ∨ True)) ∧ (p5 → (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185360247893314274792037082739 : ((p4 ∧ (p1 ∨ ((p2 ∧ ((p4 ∧ (p2 → True)) ∨ p2)) → False))) ∨ ((p5 ∧ ((p1 → ((False → p1) ∨ True)) → False)) → ((False ∨ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171995104004019232265960292592 : ((((((p5 ∧ p2) ∨ True) ∧ ((False ∨ (p5 → p4)) → False)) ∨ p4) ∨ (p5 → p5)) ∨ ((p2 ∨ (p1 ∨ True)) → (p2 → (False → (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265707991200433825082718954212 : (True ∧ (p3 ∨ (((p4 ∨ (p1 ∧ ((False ∨ (False → (p5 ∧ p1))) ∨ ((p3 ∧ p3) → (p1 ∧ True))))) ∧ (p5 ∨ (p3 ∨ p4))) → (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354924101314374224095047807361 : (p5 → ((p2 ∨ ((((p2 → p3) ∧ p1) ∧ p4) ∧ (p2 ∧ ((p2 ∧ (((False ∧ (p4 ∨ False)) → True) ∧ ((True ∨ p3) → p1))) ∧ p4)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136220126863572419116044972447 : (((((p2 → (p2 ∨ p2)) → p5) ∨ p3) ∨ (p5 ∧ ((p5 ∨ False) → (((p3 ∨ (p5 ∨ (p2 → p3))) ∨ p4) → False)))) ∨ (p5 → (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41955006065112295747427971023 : ((((p3 ∧ False) ∧ (p2 ∧ ((p1 ∧ ((p1 ∨ p2) → (p2 ∨ p5))) ∧ ((False → False) ∨ ((((False → p3) ∧ p3) ∧ p3) → p3))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23343621606220173419656707968 : ((((False ∨ (p2 → p2)) ∨ p3) ∧ (((((p2 ∧ (True ∨ (p4 ∨ p2))) ∧ p1) ∨ p5) ∧ (True → (((p1 ∨ False) → p1) → False))) ∨ True)) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344706438654876942486316401505 : (p2 → (p3 → ((((((p4 → (True → p2)) → p1) ∨ p4) → (((p5 ∨ ((p2 ∨ p1) ∧ False)) ∨ p3) ∧ p4)) ∨ ((p4 → p4) ∨ p1)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255938234721079921300239611437 : ((True ∨ p2) → ((((True → p2) ∧ p5) ∨ False) → (((True ∨ ((p3 ∧ False) ∧ p1)) ∧ (True ∧ ((((p4 ∨ p2) → p3) ∧ p5) ∧ p4))) ∨ p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56278495062448394286275643814 : (((p5 → ((p4 ∧ p1) ∧ True)) ∨ (p3 ∧ (True → ((p5 → (p4 ∧ ((p5 ∧ p1) ∨ p4))) → (True → (((p4 → p5) ∧ p5) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682050334374977010627925221103 : (((((p2 ∨ ((p5 → (((p4 ∧ p1) ∧ True) → (False ∧ p2))) ∧ (p2 ∨ (False ∧ p3)))) ∨ True) ∧ (False ∨ (True ∨ ((True → True) ∨ p5)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786905583322948033142514633177 : (((p4 ∨ ((p5 → (False ∧ False)) ∨ ((((((p2 ∧ False) → p5) → False) ∨ True) ∨ p3) ∨ (p1 ∧ ((((p5 → p1) ∧ p1) → True) → False))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151655042633481654551128915278 : ((((((p2 ∨ ((p5 → p5) ∨ True)) → p4) ∧ (True ∨ p1)) ∧ (p5 → (p1 ∨ p2))) ∧ ((p2 → False) ∧ p5)) → ((False ∨ (p1 ∨ p2)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h7.left
        let h14 := h7.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h15 : (p2 ∨ ((p5 → p5) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h7.left
        let h19 := h7.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h20 : (p2 ∨ ((p5 → p5) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h21 := h10 h20
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h24.left
        let h31 := h24.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h32 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h33 := h30 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h24.left
        let h36 := h24.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h37 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h38 := h35 h37
        -- False on the left can always be used.
        apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166712139149180827580186082215 : ((p3 → ((((((p1 ∨ True) → p3) ∨ p5) ∧ p5) ∨ p1) ∧ (((p4 ∧ True) ∨ p4) ∨ p3))) ∨ (p5 ∨ ((True ∨ p3) ∨ (p5 → (p2 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126625972416781653323902991248 : ((p3 ∧ ((True ∨ p4) → (((False → (((p5 → p5) ∧ p3) ∧ (p1 → (p5 ∧ p1)))) ∧ (False ∧ (p3 ∨ (p5 ∧ True)))) ∧ p3))) → (False ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135877829162736824750189188248 : ((((p5 → p2) ∨ (p1 ∨ (True → (p1 ∨ ((False ∨ False) ∧ p3))))) ∨ ((p5 → False) ∧ (p1 ∨ (p5 → (p3 ∨ p3))))) ∨ ((p4 ∧ p3) → p4)) := by
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
theorem thm_5_vars_319307809049074302165036059560 : (p4 ∨ ((((p4 ∨ p5) ∧ ((p2 → (True → True)) → False)) ∧ (True → ((p4 ∨ p5) ∨ p3))) → ((True → ((p4 ∧ p1) ∨ p5)) → (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → (True → True)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h9
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h14 : (p2 → (True → True)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h14
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871640521841430983694179434629 : ((((p3 ∨ ((p3 ∨ (((p4 ∨ p4) ∨ True) ∨ (p3 → ((((p1 → False) ∧ p5) ∧ (p5 ∧ p3)) → (p4 → p3))))) ∨ (p4 → p2))) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p3 ∨ (((p4 ∨ p4) ∨ True) ∨ (p3 → ((((p1 → False) ∧ p5) ∧ (p5 ∧ p3)) → (p4 → p3))))) ∨ (p4 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219317626188016307121878979138 : ((p2 ∨ (True ∧ (p4 ∨ True))) → (((p3 ∨ (p2 ∨ ((p2 ∨ p3) ∧ (p5 ∨ (p2 ∧ (p1 ∧ p2)))))) ∧ (True ∧ True)) ∨ ((True ∨ False) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
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
theorem thm_5_vars_641747813548927367332181267724 : (((((p3 ∨ p3) → ((p5 → (p2 ∧ ((p2 ∨ p5) ∧ (((((p1 ∨ p2) → p3) ∨ (True ∨ p2)) ∨ (p4 → p4)) ∨ p4)))) ∨ p1)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173932175849978776658412800459 : ((((((((p4 → p3) → p2) ∨ p1) ∨ (p4 ∨ p2)) → p4) → (p4 ∨ False)) → p4) → (((p5 → p3) → (p3 ∧ p3)) ∨ (False → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159315499359393437913820468977 : ((p5 → (((((p4 ∨ False) ∧ ((p3 → p1) ∧ p1)) → p3) ∨ (p3 ∧ False)) ∧ ((False ∨ p5) ∧ p1))) ∨ (((p5 → True) ∨ (True ∧ p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186278962341953941123436076009 : ((((p2 → (((p5 → p3) ∨ p1) ∨ (p5 → p1))) ∨ p2) → p4) → (((((p3 ∨ True) → p5) ∧ True) ∨ ((p5 → (False ∨ p4)) ∧ False)) → p5)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326855218377749008637770054401 : (True → (((True → (((False → p2) ∨ ((((p2 ∨ p1) → p3) ∧ (False ∨ p4)) ∨ (True ∨ (((p5 ∧ p5) ∨ p4) → False)))) → False)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110761276156736562230263643272 : ((((p1 ∨ ((p4 → False) → ((p1 ∨ (((True → p1) ∨ (p2 → (p1 ∧ (p5 → p2)))) → False)) ∧ (p1 ∨ p1)))) ∧ p3) ∧ True) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623872942971906354703557283255 : ((((p1 ∨ (p1 ∨ ((p2 ∨ p5) ∧ ((((p1 ∨ p2) ∨ p4) ∨ (p4 → (p4 ∧ p1))) → (False ∨ ((p4 ∨ p4) ∧ (True → p3))))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_33159903721810427012814752501 : ((p3 ∨ (p2 ∨ ((((True ∨ p3) ∧ (True → p4)) ∨ (p1 → ((((True ∨ False) → (False ∧ p1)) ∧ (p2 ∨ False)) ∨ p1))) ∨ (p3 ∧ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58975824959979018255687015234 : (((p2 ∧ p4) ∨ ((p3 → (p5 ∧ ((False ∧ p3) ∨ ((p1 ∧ False) → p2)))) ∨ ((((p2 ∧ p5) ∨ (p5 ∨ p3)) ∨ (True ∨ p1)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40314141724708568329053897821 : ((((((p2 → True) ∧ (((((False ∧ (((False ∨ ((p4 ∨ p1) ∨ p3)) ∧ False) ∧ True)) ∧ p4) ∧ True) ∨ p3) ∧ False)) ∧ p1) ∨ True) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19045562698865170160224905912 : ((((((((True ∧ p1) ∧ p3) ∧ p5) → (p1 ∨ (True ∨ True))) ∨ (p1 → (p2 → p5))) → p1) → (((p2 ∧ (True ∧ p4)) ∧ False) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∧ p1) ∧ p3) ∧ p5) → (p1 ∨ (True ∨ True))) ∨ (p1 → (p2 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173165976303436810759820399205 : ((p4 ∨ (((p3 ∧ ((p1 ∨ p4) ∧ p5)) ∧ (False ∨ (p2 ∧ (p5 → p1)))) ∧ p5)) ∨ (((p5 → True) ∨ ((p4 → p2) ∨ p4)) → (True ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618873209961778204445036954349 : (((((p5 ∨ (True ∨ p3)) ∧ (p5 ∧ ((p1 ∨ ((p4 ∨ ((p2 → False) ∨ (p4 ∧ (((p4 ∨ p5) → p5) → p4)))) ∧ True)) ∧ p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186661713562974733836422383154 : ((((p2 → ((True ∨ p5) ∨ p2)) → p5) ∧ (p5 → (p5 ∧ False))) → ((p2 ∧ (p1 ∧ (p4 ∧ ((p1 ∧ ((p3 ∧ p2) ∧ p3)) ∧ p1)))) ∨ True)) := by
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
theorem thm_5_vars_111854604877723518983887548847 : ((((False ∨ (False → ((p5 → p1) → ((p1 → (False ∧ p2)) ∧ ((p3 → (p4 ∧ p4)) ∨ p4))))) → (False ∨ (False ∧ p2))) ∨ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230286244483639373193070745652 : (((p1 ∨ True) ∧ p1) → ((p4 ∧ ((p3 → p2) ∧ ((((((p5 ∨ p4) ∧ False) ∨ p5) → (((p1 → p4) → p4) ∧ p1)) → p4) ∨ p5))) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233308814761489203657558583036 : ((True ∨ (p4 ∨ p4)) → (p1 ∨ ((((p2 ∧ p3) → ((True ∧ (True ∧ p1)) ∧ p4)) → p2) ∨ ((p1 ∨ False) → (((p1 ∧ p4) → p1) ∧ True))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207907543177901556801754196702 : (((p2 ∧ (p4 → p3)) ∧ (False ∨ p2)) → (((p5 ∨ ((((p3 ∨ (((p1 → False) → p5) → p5)) ∨ (p1 ∧ p1)) ∨ p1) ∧ p1)) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172240098771930354951343358974 : ((((p5 ∧ ((p5 ∨ True) ∨ p4)) ∨ (p2 ∨ p3)) ∧ ((p5 ∨ (True ∨ False)) ∨ p2)) ∨ ((((False ∧ p5) ∨ True) ∨ (p2 ∧ False)) ∨ (p2 ∨ p4))) := by
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
theorem thm_5_vars_654465139899052916525882875994 : ((((((p5 ∧ p5) ∨ ((p5 ∧ (p5 ∧ ((p3 ∧ ((p3 ∨ (p1 ∨ p1)) → p4)) → ((p4 ∨ False) ∨ p4)))) → False)) ∨ False) ∨ (p4 → p4)) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21494233578126544036153342200 : (((((p5 ∨ p5) ∨ p1) ∨ (p4 → ((p1 ∧ p1) ∨ p5))) ∨ ((False ∨ True) ∨ (((True → (p1 → p5)) ∧ ((p3 ∨ p5) ∨ False)) ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147468098329821382358047923480 : (((False ∧ ((((True ∨ (p1 → p2)) → False) ∧ (p5 → False)) ∨ ((p1 ∨ True) ∨ ((p2 ∨ p5) → p5)))) ∨ p1) ∨ (p3 → ((p2 ∨ False) → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660623854448551978081115974676 : ((((((p2 → (p5 ∨ (p3 ∨ ((p2 → (p2 ∧ True)) ∧ (p1 → ((True ∨ p3) ∧ (p3 ∨ p4))))))) → (p3 ∧ False)) → p4) → (p4 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116244980302985331378479259770 : ((((p5 ∨ p2) → p3) ∨ (((False ∨ (False ∨ False)) ∨ True) ∧ ((((p4 ∨ p3) → p1) → p3) → ((p2 ∨ p1) ∨ (True ∨ p4))))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232214477127516571373731815200 : (((p1 → True) → False) → (((p3 ∨ (p5 → p1)) ∧ (p5 ∧ False)) ∨ (p5 → ((p1 → (True ∧ True)) ∧ ((p5 ∨ (p5 ∨ p3)) → (p5 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314670163495883559425202039054 : (p3 ∨ ((p5 → ((p1 ∨ p4) ∨ ((p1 ∧ (False → (True ∨ (p2 → (p2 ∧ p1))))) ∧ p1))) ∨ (p3 → (p1 ∨ ((False ∧ p5) → (True ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323268107685682393269754477836 : (p5 ∨ ((p3 ∨ ((p5 ∨ p5) → (((p4 → (p3 ∧ p5)) ∧ ((p3 ∧ p1) → p5)) ∧ ((((True ∨ p3) ∨ p5) ∨ p1) → p2)))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147899083853620715613900511047 : ((((p5 ∨ ((False ∨ ((p5 → p2) → p3)) ∧ ((p3 ∧ ((p3 ∧ p1) ∨ p4)) → p2))) ∨ False) ∧ (p3 → p1)) ∨ (((p1 ∨ p2) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669344530776275720421120906190 : ((((((p3 ∨ (True ∧ p1)) → ((p5 → p2) ∧ ((((p3 → True) → (p5 ∧ p5)) ∧ False) ∧ p1))) ∧ (False ∨ False)) ∨ (p4 → (p4 ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45813790352279008122210608468 : (((p1 → (p2 → (((((p1 ∧ (p1 → ((p4 ∧ True) ∨ p5))) ∨ (p3 → True)) ∨ ((p4 ∨ p4) ∧ p2)) → p4) ∧ (p5 → p3)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66040271777393916960474416382 : ((p5 ∨ ((p2 ∨ (((p1 ∨ (p1 ∨ p3)) ∨ p3) ∧ ((((p4 ∨ ((p1 ∧ p2) → p2)) ∨ (p2 → p3)) → (p4 ∨ p2)) ∧ p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248887924714335272568271405121 : ((p3 ∨ p5) ∨ ((p3 ∧ ((((p1 ∨ (p5 ∧ False)) ∧ (p5 ∧ p5)) ∧ False) → True)) → (p5 ∨ (p3 ∧ ((p1 ∧ p1) ∨ (False → (True → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113789142726602918788580032316 : ((((p2 ∨ p5) ∧ (True ∨ ((p2 ∨ p1) ∨ (p2 ∧ (p2 ∧ (True → (p4 → (p5 → ((p4 ∨ p4) ∨ p2))))))))) → (True → p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134882649080930779498513670538 : (((p3 → (((True ∧ (p3 ∨ ((((p1 ∧ p4) → p4) ∧ False) ∧ p1))) ∨ p2) ∨ (((p2 ∨ True) ∧ p5) ∨ False))) → p4) ∨ ((p3 ∧ p1) → p1)) := by
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
theorem thm_5_vars_213159383905502267171061343933 : ((((p2 ∧ p5) ∨ p4) ∧ p3) ∨ (False ∨ ((p1 ∧ (p4 → (((True ∨ (p1 ∧ False)) ∧ (False → p5)) ∨ True))) → (True ∨ ((p4 ∧ False) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



