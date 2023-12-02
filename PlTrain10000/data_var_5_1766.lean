variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209482690999321164782445677240 : ((p3 → ((p5 ∨ p2) → (p4 → p2))) → (((p2 ∨ (((p4 → p1) ∨ False) ∨ True)) ∧ p4) ∨ ((p2 → p5) → (p1 → (p5 ∨ (p1 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305674496760666278075944030531 : (p1 ∨ (((((p5 → p5) ∧ p5) → (p5 → True)) ∧ (True → False)) ∨ ((((p4 ∨ (p3 ∨ (p3 ∨ p4))) ∧ p5) ∧ (p5 → p4)) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201036288837477983891482207377 : ((p4 ∨ ((p3 ∨ (p2 → p4)) → (p4 → p5))) → ((p5 ∧ ((p4 → (((p2 ∧ True) → p2) ∨ p4)) ∧ (p2 ∧ (False ∨ (p2 → p5))))) ∨ True)) := by
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
theorem thm_5_vars_596007937306378274666545726876 : ((((((p5 ∨ (p4 ∨ (((p3 → p4) → p2) → True))) ∧ True) → ((p1 ∨ ((p1 → True) → p3)) ∧ ((p4 ∧ p5) → (False → p2)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320471130812307632264208607282 : (p4 ∨ ((p1 → p3) → (((p2 → (p4 ∧ (p1 → (False ∧ (p4 → p3))))) ∨ (p3 ∨ (((p4 ∧ p4) ∧ (p2 → p3)) ∨ (p2 ∧ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723020763160320861128100963636 : (((((p1 ∨ False) ∨ p1) ∧ (p3 → (p1 ∨ ((p5 ∨ (True ∧ ((False ∨ p5) → ((p2 ∨ (False → (True ∧ p4))) ∧ (p4 → p2))))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784753324491960952319580869242 : (((p3 ∨ (p5 ∨ (True → (((((p5 → True) → ((p3 ∧ (p4 ∧ True)) ∨ p1)) ∨ True) ∧ ((p3 ∨ ((False → p1) ∧ True)) ∧ True)) ∨ p1)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322474830696205214392249157784 : (p5 ∨ (((False ∨ p3) ∧ ((((p3 ∨ (False ∧ ((((p1 ∨ p4) ∨ (p4 ∧ (p4 ∨ p2))) → p3) → p5))) ∨ False) ∧ p3) ∨ (p4 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262235381103639058894864926120 : (True ∧ (((p2 ∨ (p5 → (p1 ∨ (((p5 ∧ p3) ∨ (((p3 ∧ ((p4 → p3) ∨ (p1 ∧ True))) → p2) → False)) ∧ True)))) ∨ (p4 ∨ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38177548844374765662519206321 : (((((True ∧ p2) → ((p3 ∨ False) ∨ (p3 ∨ ((p1 → (False → False)) → (((True ∨ p4) ∧ p1) ∨ True))))) ∨ ((p2 ∨ p5) ∨ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353483512938075149651495930262 : (p4 → (p2 ∨ (((False ∨ ((True ∧ (((p1 → p3) → p3) ∨ (False ∨ (False → (p2 ∧ (False ∨ p1)))))) ∧ p1)) ∨ (p2 → p4)) ∨ (True ∧ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206091147172531710290965931405 : ((p3 ∧ (p1 ∨ (False ∨ (p1 ∧ False)))) ∨ ((((False ∧ ((True ∧ (p4 ∨ True)) ∨ ((True → (p3 ∧ False)) ∧ p1))) → (p5 ∧ p3)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621300699326440766610367533101 : ((((True ∧ ((((p1 → False) ∨ ((False ∨ False) → p4)) ∨ True) ∧ (p1 ∨ ((p3 → (False ∧ p2)) → ((True → (p5 ∧ p2)) ∨ True))))) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204090194317784620889990158219 : ((p5 → (False ∨ ((True ∨ p4) ∨ p2))) ∧ (((p2 → True) → ((((p4 ∨ (False ∨ p3)) ∧ p4) → ((False ∨ p2) ∨ p5)) ∨ (p1 ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66486402004549381707482290962 : ((True → ((((p2 ∨ ((False ∨ ((True → p3) → (p2 ∧ p5))) ∨ (p5 → (False ∨ p5)))) → (p2 ∧ p2)) → ((p5 ∨ p4) ∧ p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165948165477705254514623094212 : (((p2 ∨ p5) ∧ (p3 → ((p5 → ((True → True) → False)) ∧ ((p5 → (p1 ∨ p3)) ∧ True)))) ∨ (p2 → (((p4 ∨ False) → (p1 ∨ p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300066539456006743199169948310 : (False ∨ ((((p1 ∨ (p2 → ((True ∧ p1) ∨ p2))) → (p5 ∧ (p3 → (False ∨ ((p4 ∨ (p2 ∨ False)) → (p1 ∧ p1)))))) ∨ True) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246512383042702417815998322810 : ((p5 ∧ p1) ∨ ((p3 ∧ (True ∧ (((p1 → (p4 ∧ p1)) ∨ ((False ∨ p1) ∧ p2)) → (((p2 ∧ p4) ∨ False) ∧ p4)))) ∨ (p5 ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76317123759146574457083402413 : (((((p5 ∨ p3) → (((p2 ∧ ((((False ∨ p5) → p3) ∨ (p2 ∨ (p2 ∧ p1))) ∨ (p3 ∧ p1))) ∨ False) → p5)) ∨ (True ∨ p3)) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p3) → (((p2 ∧ ((((False ∨ p5) → p3) ∨ (p2 ∨ (p2 ∧ p1))) ∨ (p3 ∧ p1))) ∨ False) → p5)) ∨ (True ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112560209774981281915540699334 : ((((False ∧ ((((p1 → (p5 ∨ (p3 ∨ (p5 ∨ p1)))) → p4) ∨ False) ∨ ((((p2 ∧ p5) ∨ True) → True) ∧ p3))) → False) → p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144755127270474067635635052817 : ((((p3 → ((p1 → (p1 ∨ p3)) ∧ ((((p2 ∧ p2) ∨ p1) → False) → p1))) ∨ p5) ∨ ((p3 → True) ∧ True)) ∧ ((True ∧ p5) → (p1 ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257792255501670576859950115156 : ((p3 ∨ p5) → (((p3 ∨ ((((p5 ∨ (((True ∧ p5) ∨ False) → False)) ∨ p5) ∨ p1) ∧ (p5 → ((p3 ∧ p1) ∨ p4)))) ∧ (p5 ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_134541608399658836924020606735 : (((((p3 ∨ ((p5 ∨ (True ∨ (p3 ∧ ((True → True) → p3)))) ∨ p4)) ∧ ((p1 ∨ (p4 ∧ False)) ∧ True)) → p2) → p5) ∨ (False → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65174493888816961926155064823 : ((p3 ∨ (((((p3 → p1) → ((((True → p3) ∨ p3) → False) ∧ p4)) ∨ p3) ∧ ((((True ∨ p4) ∧ (p3 ∧ p4)) → p1) ∧ False)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318881035606327466559647565425 : (p4 ∨ ((((p2 → p5) ∨ (False ∧ False)) ∧ ((p1 ∧ ((p2 ∧ p2) ∨ (p3 ∨ p1))) ∨ ((True → (False ∨ p2)) ∨ True))) ∨ (False → (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_313979901456003086794805854890 : (p3 ∨ (((p3 → ((p1 → (p4 ∨ False)) → (p3 ∧ p4))) ∧ (p5 ∨ (((p3 ∧ p5) → p4) ∨ (((False ∧ p1) → p5) ∧ p5)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190942306052120363681871054029 : ((((True → p5) ∨ (p3 ∨ False)) ∧ ((p3 ∧ True) → p2)) ∨ ((p1 ∧ p2) → (p1 ∧ ((p5 ∧ ((True → p3) ∧ True)) ∨ (p3 ∨ (p4 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57778016781705424202223295903 : (((True ∧ (p2 → p3)) → ((True → p1) ∧ ((p3 → p1) ∨ ((((p4 ∨ p5) ∨ p4) ∨ ((p4 ∧ p3) ∧ False)) ∨ ((p2 ∨ True) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136008667645428040833922799644 : (((p5 → ((True ∧ ((p5 ∨ p3) ∧ (False ∨ p4))) ∨ p4)) ∨ (p5 ∧ (p1 ∨ ((((False → False) ∧ p4) ∨ p4) ∨ False)))) ∨ (p3 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228464481013040181859810236400 : ((False ∨ (p4 ∨ p1)) ∨ ((True ∧ (p5 → ((True ∧ ((p2 ∧ p4) → (p4 ∨ p3))) → (p3 → (True ∧ ((p4 ∨ p5) → False)))))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45952701181731465093418122628 : (((p5 → ((False → (p3 → (p5 ∨ (True ∨ (p1 → ((p4 ∧ False) → p2)))))) ∨ (p4 ∨ (((p2 ∨ (p3 ∨ False)) ∧ p5) ∧ False)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217818554850855012146151697511 : (((p3 ∨ (False ∧ p1)) → p4) → (((False → p1) → ((p4 → ((p3 ∨ p5) ∨ p4)) → ((p2 → True) → ((p2 ∨ p1) ∧ (False ∧ p2))))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → ((p3 ∨ p5) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314841778380581752700834567801 : (p3 ∨ (((p1 ∨ p3) → ((((p1 ∨ p1) ∧ True) ∧ (p4 ∨ False)) ∧ p5)) ∨ ((p5 ∨ True) → ((True ∧ (p2 ∧ p5)) ∨ (p5 → (True ∨ p2)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310936271251223826154809118951 : (p2 ∨ ((True ∨ False) ∧ ((False ∧ p3) ∨ (((p5 ∨ ((True ∨ p3) → (p2 → p3))) ∨ (p1 → (False ∨ p1))) ∨ ((p4 ∧ False) ∨ (True ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122839205112634850482831280516 : (((((p2 ∧ (False ∧ (p4 ∧ ((True ∧ (((p4 ∨ False) → p3) ∨ False)) ∧ True)))) → p4) ∨ (False → p4)) ∧ (p5 ∧ (True → p4))) → (p4 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322413314222305101667069468123 : (p5 ∨ ((((p2 ∨ (p1 ∧ (p2 ∧ True))) ∨ (True ∧ (p3 → p4))) ∨ ((p4 ∨ (False ∧ False)) ∨ ((p4 ∧ ((p4 ∨ True) ∨ True)) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42975498304118110977088714618 : (((p5 → (((p5 → p1) ∧ (((False → ((p2 → p4) ∧ p2)) ∨ (p1 ∧ True)) ∨ p4)) ∧ ((p3 → p1) → ((p1 ∨ p2) ∧ p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256333765593910416431081841549 : ((False ∨ p2) → (((((p3 ∨ ((True ∨ p5) → ((p3 ∨ (False ∧ False)) ∧ ((p3 ∧ p2) → True)))) → p5) ∨ (False → (p3 ∨ False))) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248429516292824748232078119608 : ((p2 ∨ p4) ∨ (p2 → ((((p5 ∨ (((p5 ∧ p5) ∨ (False ∨ p2)) → (p5 ∧ p4))) ∧ (p2 ∨ ((p2 → False) → p3))) ∧ (p1 → p5)) → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : ((p5 ∧ p5) ∨ (False ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : ((p5 ∧ p5) ∨ (False ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308837088933662367148048517669 : (p2 ∨ (((((True ∨ p3) ∧ ((p2 ∨ (((p3 → ((p4 ∨ (p1 ∨ p1)) → p4)) ∧ p1) ∧ p2)) ∨ ((p5 → p2) → p2))) ∨ True) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p3) ∧ ((p2 ∨ (((p3 → ((p4 ∨ (p1 ∨ p1)) → p4)) ∧ p1) ∧ p2)) ∨ ((p5 → p2) → p2))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330500871553529537655707477725 : (True → (p4 ∨ (((((p3 ∨ (p5 → True)) ∨ p2) ∨ (p5 → False)) → (p5 ∧ False)) → ((p5 → ((p3 ∧ ((True ∧ False) → False)) ∧ False)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ (p5 → True)) ∨ p2) ∨ (p5 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175291678743401165580909637355 : ((p3 ∨ ((True ∨ (((p5 ∧ True) ∧ False) → True)) → (True ∧ ((p1 ∨ p3) ∧ True)))) → (p4 → (((p1 ∨ p1) → False) → ((True → p1) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p1 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62620574132737800810404135572 : ((p4 ∧ ((((p3 → (((p5 → p3) → p2) ∨ p5)) → ((((p3 ∧ (True → False)) → p1) → p2) ∧ p2)) ∨ ((p4 ∧ False) ∨ True)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757200709536305005458691226673 : (((p1 ∧ ((p1 ∧ False) ∧ ((p3 → (p5 ∨ ((((p4 → (p3 ∧ p1)) → False) ∧ p2) ∧ ((False → False) ∧ p1)))) → (p5 → (p4 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148218843222009723834519285325 : (((((((p3 ∧ p4) ∨ p1) ∧ (p1 ∨ True)) ∧ ((p5 ∨ p3) ∨ (True → True))) ∧ p1) ∨ (p1 ∨ (p2 ∧ p4))) ∨ (((p4 ∨ p4) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310306014215533639302088851965 : (p2 ∨ (((p2 ∧ p1) ∨ ((p4 ∨ (False ∨ False)) → (p5 ∧ p1))) ∨ ((p3 ∨ (((p1 → (((False ∨ True) ∧ p4) ∧ p3)) ∧ p1) → True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148891923237632564012664380522 : ((((p3 ∨ p2) → (False ∧ p1)) ∨ (True → (p2 ∧ (p2 → ((p2 → (((p5 ∧ p1) → p5) → p4)) ∨ False))))) ∨ (p3 → ((False ∧ p5) → p5))) := by
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
theorem thm_5_vars_228871383538913684469362110583 : ((p4 ∨ (True ∧ p3)) ∨ (p2 ∨ ((True ∧ p4) → ((True ∧ (((p2 ∨ False) ∨ ((p1 ∨ (True ∧ p2)) → p2)) ∨ p4)) ∧ ((False ∧ p1) → p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754487448737685403381582747344 : (((False ∧ (True ∧ (p5 → ((p3 ∨ (True → (True ∨ p3))) ∧ (((p2 ∧ (((p4 ∨ p5) ∧ p4) ∧ ((False → p3) ∧ p2))) → True) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263480960424353423807747438761 : (True ∧ ((True ∧ (((p1 ∨ p3) ∨ ((((p1 ∨ True) ∨ (p5 ∧ p2)) ∧ True) ∧ (((p3 ∨ False) → True) → p3))) ∧ True)) → ((p4 ∨ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246091466800167066057436413117 : ((p4 ∧ p1) ∨ (((((((p4 ∨ p4) ∨ (p1 ∧ False)) ∧ (True → p3)) → p1) ∧ p4) ∨ (p3 → p1)) → ((p3 ∧ (p4 → True)) ∨ (False ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599107452336284885640932616044 : (((((False → p2) ∧ (((p1 → (True ∧ p3)) → ((p4 ∧ p3) ∧ (p3 ∧ p3))) ∨ ((p4 ∨ (p5 ∨ (p4 ∨ p4))) ∨ (p4 → p3)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731509228437066677160240247339 : ((((False → (False ∧ p5)) → (p4 ∨ (((p3 → p2) → ((False ∨ ((p4 ∧ (p2 ∧ p4)) ∧ p1)) ∨ True)) → (p4 ∧ ((p5 ∧ False) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686585640478851207074034208868 : (((((True ∧ p5) ∨ (((True ∧ False) → ((p5 ∨ p4) ∨ p5)) ∧ (p3 → ((p4 ∨ p2) → p3)))) → (p2 ∧ (((p1 ∧ True) ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147193383202702124114336439093 : (((p5 ∨ ((((p4 → p3) → (p3 ∨ (p1 ∨ p3))) ∨ (p1 ∧ (((p2 → p3) → p5) → p4))) → p2)) ∧ p5) ∨ (False → ((False ∨ True) → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773950256849297871351931029352 : (((False ∨ ((p4 → (((p5 ∧ (p3 ∨ (p4 ∨ ((p1 ∧ p5) → (p3 ∨ True))))) → (p2 ∧ p2)) ∨ (((False ∨ p3) ∨ False) ∨ p4))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787611336535865200215742993982 : (((p4 ∨ (p2 ∨ (True → (p4 ∧ (((False → (p5 ∧ (p1 → ((p4 ∧ p2) → (p2 ∧ p2))))) ∨ True) → (p2 → (True → (p1 → p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165226407775554968468559613777 : ((((False ∧ (p4 ∨ False)) ∧ (True ∧ (p3 ∨ ((p2 ∨ (False ∨ p3)) ∨ True)))) ∨ (p5 ∨ True)) ∨ (((p5 ∧ False) ∨ p1) → ((True ∧ p5) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111993640615588431569769903781 : ((((p1 ∧ (p1 ∨ (p1 → p1))) ∧ ((p1 ∧ p1) ∧ (p2 ∧ ((p5 ∧ ((False → ((p3 ∧ p2) ∨ True)) ∧ p2)) ∨ False)))) ∨ True) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33066714099088502692487974150 : ((p3 ∨ ((p5 ∧ (p4 → p1)) → ((((True ∧ p2) ∧ (p3 ∧ True)) → (p2 ∧ False)) ∨ (p1 ∨ (((p5 ∧ (p2 ∨ False)) ∨ p5) ∨ p3))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170629277973088708589515480375 : (((p2 ∨ True) → ((True ∧ (p5 ∨ (False ∨ ((p5 → p3) ∨ (p5 ∨ True))))) ∨ p3)) ∧ ((p4 → True) ∨ (p2 → (((True ∨ p1) ∧ True) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133181768532932832766573900239 : ((p1 → ((((p4 ∨ (((p1 ∧ p5) → False) ∨ False)) ∧ ((p5 → p2) ∨ (p3 ∨ p4))) ∨ (False → (p2 → False))) ∧ True)) ∧ (p5 → (False ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190356993481098727027911527228 : ((((p4 → (p4 ∧ p5)) → ((False ∨ True) ∧ False)) ∨ p1) ∨ (p1 → (True → ((False ∧ (p1 ∨ ((True ∨ (False ∨ p4)) ∧ True))) ∨ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50944582497572020445582163448 : ((((((p5 → (p4 ∨ (p4 → False))) → p4) ∧ True) ∧ (True ∧ (((p3 → p4) ∨ p5) → p5))) ∧ ((((True → True) ∨ True) ∨ p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348972072151217495639159930912 : (p3 → (p4 ∨ (((p5 ∧ (p5 ∨ p2)) ∨ ((p5 → ((((((True ∨ p3) ∧ (p3 ∧ False)) ∧ p2) ∧ p5) ∧ (p2 ∧ False)) ∧ p2)) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67946253477228406774684966661 : ((p2 → (((True ∧ ((p3 → p2) ∧ p2)) → False) → ((False ∧ (False ∧ (p3 ∨ ((p4 ∧ True) ∨ (p1 → p4))))) ∧ ((p2 ∧ False) → p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ ((p3 → p2) ∧ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ ((p3 → p2) ∧ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (True ∧ ((p3 → p2) ∧ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52954896738169248527582779699 : ((((True ∧ ((True ∨ (p5 ∨ p4)) ∧ (False ∨ (p4 ∧ p4)))) ∨ p5) ∧ (False ∨ (p2 ∧ (p3 ∨ ((p3 ∨ (True ∨ (False ∨ p1))) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741861492536067864304301041868 : ((((True → p5) ∨ ((((p1 ∧ (p1 → ((p4 ∨ False) ∨ p3))) ∧ (False → ((p1 ∧ p1) → p3))) ∨ p5) → ((p3 ∧ False) ∧ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299402997811737001534976925301 : (False ∨ ((p1 ∧ ((False ∧ p3) ∧ ((p1 ∨ (((p4 → p3) ∧ (((p3 → (p1 ∧ p5)) → (p1 → False)) ∨ True)) ∧ (p1 ∨ True))) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193065825458000403981191610232 : (((((p3 ∨ False) ∨ p3) ∨ p4) ∧ (p3 → (p5 → p5))) → ((p4 → ((True → (False ∧ (p4 ∧ p4))) ∧ (p1 ∨ p2))) ∨ ((p2 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384567516602292980817451817926 : ((((((p3 ∨ (False → (p1 ∨ False))) ∨ ((False ∨ (p4 → (p3 → (p4 ∨ (((p2 → p4) ∧ p1) ∨ (p1 ∨ p4)))))) ∨ p2)) → False) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_329795763349381340083848817397 : (True → (True ∧ (p4 ∨ ((((p1 ∨ p4) ∨ (((p4 ∨ p5) → (p5 → p2)) → ((True ∨ p3) → (p5 ∨ (p5 → True))))) ∨ p1) ∨ (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148019760600165257632817207733 : ((((False ∨ (((True ∧ p5) → p1) ∨ (p1 → False))) ∧ (False ∧ (True ∧ ((p2 ∨ p1) ∨ p2)))) ∨ (p1 ∧ p2)) ∨ (((p1 ∨ p3) ∧ False) → p2)) := by
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
theorem thm_5_vars_115402184673293450971897322663 : (((False ∨ ((p4 ∧ p4) → ((True → p5) ∨ p1))) ∧ ((False → ((p3 ∧ ((p3 → True) ∧ (p3 ∧ True))) → False)) → (p5 → p1))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134219406455633221857900556031 : (((((p2 ∨ p5) → ((True ∨ p5) ∧ p5)) ∧ (((p3 → False) → (p2 ∨ p3)) ∧ (p1 ∨ ((False ∧ p2) ∨ True)))) ∨ True) ∨ (p3 ∨ (p3 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150662235089213030684960975823 : (((p4 ∨ (((p1 ∨ False) → p5) ∨ (p1 → (((p2 → p2) ∧ p5) → ((p2 → (p3 ∨ p5)) ∨ True))))) ∧ p5) → ((p1 → False) ∨ (p2 → p5))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65091523033908484471368377519 : ((p2 ∨ (p1 ∨ ((p1 ∨ ((p1 ∧ p3) → (p1 → ((p5 → p3) → p4)))) ∨ (((True ∨ p1) ∧ (p5 ∨ (p1 ∧ p1))) → (False ∨ True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53467448366368664927344562468 : ((((p2 ∨ p3) → (((True ∨ True) → p3) → (True ∧ (p4 ∨ p5)))) → ((p2 ∧ ((p5 ∧ (False → (p1 ∨ p3))) → p3)) ∨ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697032424799948612837887757227 : (((((True ∧ (p2 ∧ ((p5 → p2) → True))) ∨ ((p5 ∧ p5) ∨ False)) ∧ ((p1 ∨ (p5 ∨ (False → p3))) ∨ (False → ((p3 ∧ p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7660907829246920500059231032 : ((((((((p2 ∨ ((p2 → True) ∨ (p5 → (p4 → (True ∧ p1))))) ∧ ((p2 → (True → p3)) ∧ p5)) → p2) ∧ p4) ∧ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64580240573106457650977720033 : ((p1 ∨ ((True ∧ p3) ∧ (((((((False → False) ∧ False) ∧ ((False ∨ False) ∧ p4)) → (p2 → (p5 → p2))) ∧ False) ∨ p2) ∨ (p4 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157035433729763836306868216163 : ((((p2 ∨ p5) → ((p3 ∨ ((p4 → (True ∨ ((p4 ∨ (p2 ∧ True)) → False))) ∧ True)) → p2)) ∨ p1) ∨ (True ∨ ((p4 ∨ p3) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190356780236883055631713105074 : ((((p3 → (True ∧ p4)) → (False ∧ (p3 ∨ p4))) ∨ p4) ∨ ((p3 ∨ (p2 ∨ (p3 ∨ (((((p2 ∧ p4) → p5) ∨ p5) ∨ False) ∧ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152074354990243074770017897393 : (((True → ((p4 ∧ (p2 ∨ (True ∨ (p5 → p2)))) ∧ p3)) ∨ ((False ∨ p1) ∧ (((p5 ∨ p5) ∨ p2) → False))) → ((p1 → p1) → (p4 ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58858058153544515015988773114 : (((True ∧ p4) ∨ ((p2 ∧ (p1 → (p2 → (True → p1)))) → (((False ∨ True) → (True ∧ p5)) ∨ ((p2 → (True ∧ (p5 ∨ p1))) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191469309637600625942533298844 : ((True ∧ ((p3 ∨ ((p1 → (p5 ∧ p1)) → False)) ∧ p2)) ∨ (True ∨ (p2 ∨ (((p1 ∧ p5) → (True ∧ p1)) ∧ (False ∧ ((p4 ∨ p2) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55579606471176267108095064619 : (((p1 ∨ ((p3 → False) → (False ∨ p4))) → (((p3 ∧ p2) → (False ∨ (((True ∧ p5) → (False ∧ p2)) → (p2 ∧ (p1 ∨ True))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232831280467131965966861879938 : ((p2 ∧ (p3 ∨ p5)) → ((((p1 ∧ p1) → (p2 ∧ False)) → ((((p3 ∧ (p4 ∨ True)) ∧ (p1 → p2)) → p2) → p4)) ∨ (True ∨ (p5 ∧ p5)))) := by
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
theorem thm_5_vars_60471696737965389532213696231 : (((p5 → p4) → ((False ∧ (((p5 ∨ (p2 → False)) → p1) → p3)) ∨ ((True ∨ (False ∨ (True ∧ (p1 ∧ False)))) ∨ ((p4 → p2) ∨ p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304724328063613502651317486209 : (p1 ∨ ((((((False → (p5 ∧ False)) → (p4 ∧ (p5 → p1))) → (p4 → p5)) → p2) ∧ ((p4 → (p1 → p2)) → (p1 → p1))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39831495940175170615744379684 : (((p1 → ((p5 ∧ ((p3 ∨ (p3 ∧ (p4 ∧ ((p3 → (p5 ∧ p4)) ∨ p1)))) ∧ (p2 ∧ (p3 ∧ ((p4 ∨ True) ∧ p1))))) ∨ p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227581040195509017371249571715 : ((False ∧ (p1 ∧ False)) ∨ ((((p5 ∨ p4) ∨ p3) ∨ True) ∧ (p1 ∨ (((((p5 ∧ ((p1 ∧ p2) → (p1 → True))) → p3) ∨ p4) ∧ p3) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134269705734315829387644900559 : ((((p2 ∧ p3) ∧ ((False ∨ (False ∧ (((p3 → (False ∧ ((p3 ∧ False) → False))) ∧ p5) ∧ p4))) ∧ (p1 ∧ p4))) ∨ p3) ∨ ((True → False) → p5)) := by
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
theorem thm_5_vars_654523289738793064257639327664 : (((((p3 ∧ ((p5 → True) ∧ (((((((p3 ∧ False) ∧ p2) → (p5 ∧ p1)) ∧ True) ∨ p1) → False) ∨ (p1 ∧ p4)))) ∨ p2) ∨ (True ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_46944940661272920259934218013 : ((((p4 ∨ ((((p2 ∨ (((p3 ∧ p4) ∧ True) ∧ p3)) ∨ (p3 → ((False → (p3 ∧ p2)) ∨ p5))) ∧ p4) → False)) ∨ p3) ∨ (False → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118793319230038042135019272043 : ((p5 ∨ (p3 → (p3 → (p1 → (((True ∧ (p1 → (p5 ∨ (p2 ∨ p1)))) ∧ p5) ∨ (((p5 ∧ False) ∧ False) ∨ (False → p1))))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218397038755420764746504738614 : (((True ∧ p2) → (p3 → p2)) → (((p1 ∧ ((False ∨ p5) ∧ p4)) ∨ (((p5 → p1) ∧ p5) ∨ (p3 → (((True → p3) ∧ p1) → p3)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173931077186683919740613895217 : (((((True ∨ (((True ∨ (p1 ∧ p2)) ∧ p2) ∧ True)) ∧ p4) → (p5 ∧ p4)) → p1) → (((((p5 → p1) → p1) ∨ p5) → p1) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : (((True ∨ (((True ∨ (p1 ∧ p2)) ∧ p2) ∧ True)) ∧ p4) → (p5 ∧ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- One of the premise coincides with the conclusion.
            exact h5
        -- Conjunctions on the left can always be decomposed.
        let h20 := h7.left
        let h21 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h24.left
          let h27 := h24.right
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h28 =>
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- One of the premise coincides with the conclusion.
            exact h21
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h32 := h1 h6
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h33 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h33
  case inr h34 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h35 : (((True ∨ (((True ∨ (p1 ∧ p2)) ∧ p2) ∧ True)) ∧ p4) → (p5 ∧ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h36
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h41.left
        let h44 := h41.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h45 =>
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- One of the premise coincides with the conclusion.
          exact h34
      -- Conjunctions on the left can always be decomposed.
      let h49 := h36.left
      let h50 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h51 =>
        -- One of the premise coincides with the conclusion.
        exact h50
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Conjunctions on the left can always be decomposed.
        let h55 := h53.left
        let h56 := h53.right
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h57 =>
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- One of the premise coincides with the conclusion.
          exact h50
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h61 := h1 h35
    -- One of the premise coincides with the conclusion.
    exact h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113188258677597968088886502751 : (((((p1 ∧ (p2 ∧ (True ∧ p3))) → ((((((p5 → False) ∧ (p3 ∧ p5)) ∧ p4) → True) ∨ p5) → p5)) ∧ True) ∧ (p1 ∨ True)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66431965991861083672247309869 : ((True → ((((((((True → p4) ∨ p3) ∧ ((p4 → (True ∧ p3)) → True)) → (p5 ∨ (p5 ∨ p4))) → (False ∧ False)) ∨ p1) ∧ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



