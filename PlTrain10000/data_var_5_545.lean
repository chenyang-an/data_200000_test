variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615008052736511377630853600469 : ((((((p1 ∧ (p4 ∨ False)) → ((p4 → (((p3 ∨ (p3 → p4)) ∧ (p3 ∧ p4)) ∨ False)) → p5)) → ((p2 ∧ (True → p5)) ∨ True)) ∨ p5) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_317046492209958095396345236070 : (p3 ∨ (p4 → ((False ∨ (((p5 → p5) ∨ False) → (((p3 → True) → (p1 ∧ (p2 ∧ (p4 ∨ p1)))) → (p3 → (p2 ∨ p1))))) ∨ (p3 → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184501526114764718518625717492 : ((((False ∧ False) ∧ (p4 ∨ ((p4 → p1) → p5))) ∨ (p5 ∨ p2)) ∨ (((((True ∧ (True ∨ p2)) ∧ p2) ∨ (True ∨ False)) ∨ p5) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228211741483448530736713259998 : ((p5 ∧ (p1 ∨ p1)) ∨ ((p4 ∧ True) → (p2 ∨ (((p2 ∧ (p2 → p3)) ∨ (p4 ∧ (((p1 ∧ (p3 ∧ (p4 ∧ p1))) ∨ True) ∧ True))) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191845359335963225879464371092 : ((p3 ∨ (True ∧ (p4 ∧ (p3 ∨ (False ∨ (p4 ∨ p3)))))) ∨ (True ∨ (False ∨ (((p5 ∧ p4) ∧ p4) ∨ (p5 → ((p1 → (p4 → p5)) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53515831152811117605228637059 : (((False → ((((p2 ∨ (p2 ∧ (p2 ∧ True))) → p3) → p1) ∧ p3)) → ((((True ∧ p2) ∨ p1) ∨ (p1 ∨ True)) ∨ (p3 ∧ (p3 → p1)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_315497283481578107995187320866 : (p3 ∨ ((True ∨ (p1 ∨ p2)) → (((p1 ∧ p5) ∧ (((((p1 → p1) ∧ (p1 ∧ ((p1 ∧ True) ∨ p5))) → p2) ∧ True) ∧ p4)) ∨ (True ∨ p3)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_215609744214940134075853201843 : ((p5 ∧ (p3 → (p4 ∨ True))) ∨ ((False ∨ (p1 ∨ p3)) → ((True → (False → (True ∨ p4))) → (((False ∧ p2) ∨ (p4 ∨ (True ∧ p3))) ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
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
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112159323051684462507774302202 : (((p2 ∧ (p4 ∧ ((((p1 → (p5 ∧ (p4 ∧ (False → p4)))) ∨ ((p5 → (False ∨ (False ∧ p5))) ∧ p3)) ∧ False) ∨ p4))) ∨ False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41426431740117292677501344456 : (((((p3 → (p4 → (False ∨ (p4 ∨ ((p2 ∧ (False ∧ p5)) ∧ p5))))) ∧ True) → ((True → False) ∧ ((True → (False → p2)) ∨ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304116223896419704429466984722 : (p1 ∨ ((p3 → ((p2 ∨ False) ∨ ((True ∧ (p1 → ((((False ∨ (p5 ∧ p1)) ∧ p4) ∨ (False ∨ (False → p1))) ∧ (p1 ∨ p4)))) ∨ p3))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626727266716943073516091921468 : ((((p5 → ((((((True ∨ (p3 → p1)) → (p1 ∧ p1)) ∧ (p3 ∨ (p5 → False))) ∧ (p4 → ((p4 ∧ True) ∧ p4))) → p3) → p2)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148068146802947244141178334819 : (((p5 → (((p3 → p4) → (((p1 → True) ∧ (p4 → p4)) ∨ True)) → (p5 → (False ∧ p4)))) ∨ (p5 → p5)) ∨ (False ∨ ((p3 → False) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41526721001790009409415492144 : ((((False ∨ (p2 → (p3 ∧ (p4 ∧ (True → (p3 → p1)))))) ∧ (p5 → (((((True → p1) ∨ p1) ∧ p2) ∧ True) ∨ (p1 → False)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223641119683270467855422141053 : ((p1 ∨ (False → p2)) ∧ (True → ((True → ((((False → (p2 → p2)) → p4) ∧ (True ∨ (False ∨ False))) → False)) ∨ ((p1 ∨ (p1 ∨ p2)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244449373881993672542197627067 : ((False ∧ p2) ∨ (((((True ∧ False) → ((p2 ∨ (p1 → True)) → (True ∧ (True ∧ (p5 ∧ p2))))) → p2) ∨ True) ∨ (p4 ∨ ((p1 → False) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111311202470030564664481299501 : (((False ∧ (False ∨ ((p4 ∧ (p3 ∨ True)) ∨ ((((p3 → (True ∨ (p2 → ((p2 → p4) ∨ True)))) ∧ p5) ∧ p3) → p2)))) ∧ p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178929591816681810951641056513 : (((p5 → False) ∧ (((p3 ∨ p2) ∨ (p1 ∨ (p2 ∨ p5))) ∨ (p4 ∨ p4))) ∨ (False → ((p4 ∧ True) ∧ (p2 ∨ ((p1 → (p5 ∧ p2)) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178828480878728254210460507545 : (((p5 → (p3 ∨ p4)) ∨ ((p3 ∧ p4) ∧ ((p2 ∧ p4) ∨ (False ∨ p5)))) ∨ (((True ∨ True) ∨ p5) ∧ ((p4 ∨ p3) → (False → (True → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230480002298826400137077408965 : (((p5 ∨ p5) ∧ p4) → (((p1 → p1) ∧ (p1 ∨ ((((p1 ∨ (p4 ∨ True)) → (p1 ∨ p3)) → p3) ∨ (p2 ∨ True)))) ∧ ((p2 → p5) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47031680795773143257657404836 : (((((((((p5 ∧ p3) ∧ ((p5 → p1) ∧ p5)) ∨ ((p2 ∧ p4) → (p5 ∨ p2))) → p1) → False) ∧ p2) ∧ (p2 → True)) ∨ (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180125188864861895526285670617 : ((((((False → p2) ∧ (((p4 → p1) ∧ True) ∧ p5)) ∧ p4) → True) → False) → ((p4 ∧ ((p3 ∨ True) → ((False ∨ (p2 ∨ p5)) ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → p2) ∧ (((p4 → p1) ∧ True) ∧ p5)) ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262224805689140902747546568714 : (True ∧ (((True → (((((False ∧ p4) ∨ ((p1 ∨ p4) → (True → False))) ∧ ((p3 ∨ p3) ∧ (p3 ∨ False))) ∧ True) ∧ p4)) ∧ (p3 → p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149871810475265441825059080547 : ((p2 ∨ ((p3 → (((((p1 → True) ∧ p4) → (p4 ∨ (p4 ∨ (p1 → (p2 → p4))))) ∧ p1) ∧ p4)) → p4)) ∨ (p3 ∨ ((True ∨ p2) ∨ p4))) := by
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
theorem thm_5_vars_615760787053400035613011797904 : (((((p5 ∨ ((False ∧ (p1 ∨ (p3 ∧ p5))) → (True ∧ ((p1 ∨ p1) → False)))) ∧ ((p3 → (((p4 ∧ False) → p2) → p4)) ∨ False)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_61054118341640158133235726470 : ((False ∧ ((p5 ∧ ((p2 → p4) ∧ (((p2 → (p2 → ((p4 ∧ (False ∧ ((True ∨ p5) ∨ True))) ∨ p1))) ∧ True) → p4))) → (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171057826925603592343814159757 : ((p5 ∨ ((p3 ∨ ((True → ((p1 ∨ (p5 ∨ True)) ∨ (p2 → p5))) ∨ p4)) ∨ p1)) ∧ ((False ∧ (p4 ∨ ((p1 ∧ p2) → True))) ∨ (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44663210282012686033499301598 : ((((False → ((p5 ∧ (p2 → p2)) → True)) ∨ (((True → (((p5 → True) ∨ ((p3 ∧ p2) → True)) ∧ p4)) → p1) ∨ (False ∨ p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302032180149760237685718953148 : (False ∨ (True ∧ (((p4 ∧ p2) ∧ ((((p1 → (p3 ∧ False)) → False) → False) ∧ (p1 → p2))) ∨ ((True ∨ (p3 → (p1 ∨ (True ∧ p1)))) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355569578556133902590943421444 : (p5 → ((((p2 ∨ False) ∨ ((p4 ∨ ((p2 ∨ (False ∨ ((p5 ∧ p5) ∨ p3))) ∧ p3)) ∧ (False ∨ p5))) ∧ (p3 → (p1 → p1))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805099809506904501558636600121 : (((p3 → (False ∧ (((True → p2) → p1) ∨ (p4 ∨ ((((((((p1 ∧ False) ∧ p4) ∨ p3) ∨ (p1 ∧ False)) ∧ p5) → p4) ∨ p3) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185443344565183808983393689292 : ((False ∨ ((p1 ∨ p4) ∧ ((p5 ∨ p1) → ((p1 → False) → False)))) ∨ ((p1 ∨ (False ∨ (p1 → ((False ∧ p5) → p4)))) ∨ ((p1 ∧ p1) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47966842298908455484492614804 : (((((p2 ∨ True) → ((False → p2) ∧ (p4 ∧ (((True ∨ p1) → False) → (True ∨ True))))) ∧ (((True ∨ p4) → p3) ∨ p2)) → (p4 ∧ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h22 : (p2 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h23 := h14 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113266395893507242201628006894 : ((((p1 ∨ (p4 → (((False ∧ (True ∨ p4)) ∧ p2) ∨ ((False ∧ p4) ∧ (True ∨ True))))) ∨ ((p4 → True) → False)) ∧ (p3 → p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40787599152209140930736573329 : ((((p3 ∧ (((p5 → ((((p1 ∨ p2) ∧ True) ∧ p4) ∨ p4)) ∨ p4) ∨ (True ∨ ((True ∨ (True ∨ p4)) ∧ (False → False))))) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320101349676787866547522957552 : (p4 ∨ (((True ∨ False) → p1) → ((p5 ∧ ((False ∧ (p4 → ((True ∧ p3) ∧ True))) ∨ (((p2 ∨ False) ∧ (False ∨ p3)) ∧ (True ∨ p2)))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263993069302570461939660645662 : (True ∧ ((p2 ∨ (((p5 → ((p2 ∨ (p1 → p1)) → p1)) ∧ p5) ∧ p4)) ∨ (((p1 ∨ (p1 ∧ (p2 ∨ (p4 → p5)))) ∧ False) → (p1 ∨ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2596733694392926432687963710 : ((p5 ∧ ((((p3 → p2) → p5) ∧ False) → p2)) → (((p2 ∨ (True → ((p4 → p5) ∧ p3))) → (((False ∧ p3) ∨ p4) → p3)) ∨ p5)) := by
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
theorem thm_5_vars_319159540080093079577628070016 : (p4 ∨ ((((False ∧ p3) ∧ ((((False → True) → (p5 ∧ ((p1 → p5) ∨ False))) ∨ False) ∧ True)) ∨ p1) ∨ ((True ∨ ((True → p1) ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299383901346946373465364333477 : (False ∨ (((p4 ∨ p5) → (((p4 ∧ (p5 → (p1 ∧ (True → p5)))) ∧ p1) ∨ (((p3 ∨ ((p3 ∨ True) → True)) ∨ p5) → (False ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160133175292370383462787024243 : (((((p2 → ((p4 ∨ ((p2 → p4) → False)) ∨ ((p5 ∧ p2) ∨ p3))) → False) ∨ p3) ∧ (p5 ∧ True)) → (p3 ∨ (True → (p1 ∧ (p1 → p2))))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p2 → ((p4 ∨ ((p2 → p4) → False)) ∨ ((p5 ∧ p2) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682571080231328480183114365109 : (((((p3 ∨ (((((p2 → p4) ∧ p2) → True) ∧ p4) ∧ True)) → ((True → False) ∨ (True ∨ p3))) ∧ (((p1 ∨ p4) ∧ (False ∧ True)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147479388149951538975463260853 : (((p3 ∧ (((True → ((p1 ∧ (p2 ∨ (((True ∧ (p3 ∨ p3)) ∨ p2) ∨ False))) ∧ p1)) ∨ p1) ∧ p3)) ∨ True) ∨ (p5 ∨ (True → (False → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713097313969241942724136914243 : ((((p5 ∧ (p1 ∧ ((p2 ∧ p5) ∧ p3))) ∨ (p3 → (p1 → ((p5 ∨ (p5 → p4)) → ((False → p3) ∧ (p1 → (p1 ∧ (p1 ∨ p2)))))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692333264424166127319716249965 : ((((((((p2 ∨ p3) ∨ (p4 ∨ (p1 ∨ False))) ∧ p5) ∨ (p5 ∨ p4)) → False) ∧ ((p3 ∧ False) ∨ (p5 → ((False → p5) → (p1 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198395269242956536069929842962 : ((p3 ∧ (p3 ∨ (((p1 ∧ True) ∧ p5) ∧ p2))) ∨ (True ∨ (True → (((p4 → (p1 ∧ (p2 ∧ (p2 ∧ p3)))) ∨ (False ∨ p1)) → (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233889171075488774006128855175 : ((p4 ∨ (p3 ∨ True)) → ((((((False ∧ p3) ∨ (True ∧ (False → p3))) ∨ (p5 ∧ ((p1 ∨ (p1 ∧ p3)) → p1))) ∨ p1) ∨ p3) ∨ (p5 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57700841619148061807819217018 : ((((p1 ∧ p2) → p3) → ((p3 → (p2 ∧ (((((p4 → p2) ∨ (False ∧ ((p5 ∧ False) → True))) → p1) ∧ p5) ∧ p3))) ∧ (p1 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720759823547149859200517902630 : (((((p4 ∧ (p1 → p1)) → p2) → ((True ∧ ((p3 → (False ∨ p5)) ∨ ((True → p5) ∨ (((p4 ∨ p3) ∧ False) ∨ (p3 ∨ p2))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301263429404933039592918472536 : (False ∨ ((p4 ∧ ((p2 ∧ (False ∧ True)) ∧ p5)) ∨ (((((p3 ∨ p3) → (p5 → p5)) → (False → False)) ∧ p3) ∨ (((p2 ∧ p5) ∧ p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117386532551572077423380075295 : ((p1 ∧ (((p1 ∧ True) ∧ (p3 ∨ (((p4 ∨ (p4 → p2)) → ((((p3 ∨ p1) ∧ (False → p2)) → p4) ∧ p5)) ∧ p5))) ∧ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231387310950159779052482278526 : (((p1 → True) ∨ True) → (p1 ∨ (((p5 ∨ (((((p3 ∧ p5) → p1) ∨ (p3 ∧ False)) ∧ p3) → p4)) ∨ (((True ∨ p2) → p1) → True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628877716275879785283515210096 : ((((((((((p2 ∧ p1) ∨ ((p1 → p5) → ((p3 ∨ (False ∧ (p2 ∨ p4))) ∧ (p1 ∨ False)))) ∨ p1) → False) ∧ p3) ∧ p4) ∨ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192881097194560963323444458485 : (((p1 ∧ ((p3 ∧ (False → p2)) ∨ p3)) ∧ (p4 ∨ p5)) → ((((True → False) ∨ ((p3 ∨ p3) ∨ (False ∨ p3))) ∨ p1) → ((p3 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
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
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h1.left
          let h21 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h28 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h1.left
          let h34 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h33.left
          let h36 := h33.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h41 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h42 =>
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h43 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- False on the left can always be used.
          apply False.elim h46
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h1.left
          let h49 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h50 := h48.left
          let h51 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Conjunctions on the left can always be decomposed.
            let h53 := h52.left
            let h54 := h52.right
            -- Disjunctions on the left can always be decomposed.
            cases h49
            case inl h55 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h56 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h57 =>
            -- Disjunctions on the left can always be decomposed.
            cases h49
            case inl h58 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h59 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h60 =>
    -- Conjunctions on the left can always be decomposed.
    let h61 := h1.left
    let h62 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h63 := h61.left
    let h64 := h61.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h65 =>
      -- Conjunctions on the left can always be decomposed.
      let h66 := h65.left
      let h67 := h65.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h68 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h69 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h70 =>
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h71 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h72 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173188332172051828541347708300 : ((p4 ∨ (p5 ∧ ((p2 ∨ (p2 ∧ p2)) ∧ ((True ∧ True) → ((p2 ∨ False) → p2))))) ∨ (((p3 → ((p3 ∨ p4) ∧ False)) ∨ p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214007367625262602756401399231 : ((((p2 ∧ p4) ∧ p2) → p5) ∨ ((((((p2 ∨ (p4 → (p3 ∧ p1))) ∨ p4) ∧ True) ∧ p2) ∧ False) ∨ (((p2 ∨ (True ∨ p4)) → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True ∨ p4)) := by
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
theorem thm_5_vars_691683764604620642475522312453 : ((((True ∨ (((p1 ∧ ((False ∧ False) → ((p3 ∧ False) ∨ p4))) ∧ True) ∧ (p2 → False))) → ((p1 → p5) ∨ ((p3 ∧ p4) → (p1 ∨ p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669704291034811029450946166163 : ((((((((False → ((p2 → ((False → p5) ∨ p1)) ∧ p1)) ∨ p5) → p2) ∧ p4) ∧ ((False ∧ (p4 ∨ p2)) → p1)) ∨ ((True ∧ True) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147982647676571160755308525574 : ((((p5 ∧ ((True → p3) → (((((True ∧ True) ∧ (p4 ∨ p3)) → p1) ∨ p5) ∧ p5))) ∧ p2) ∨ (True ∨ p2)) ∨ (False ∨ (p5 ∨ (p4 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330261827478422487961051368000 : (True → (False ∨ ((p5 ∨ (((p5 ∧ False) ∧ p3) ∨ p3)) ∨ (p2 → (True → ((p3 ∧ (p3 ∧ ((p5 ∨ (p4 ∧ (p1 ∨ p1))) ∨ p2))) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313349788886958724638057367053 : (p3 ∨ ((p1 → (((False ∧ p1) ∨ ((((p4 ∨ False) → (p5 ∨ False)) ∧ p4) ∧ (p3 → p3))) ∨ (p4 ∨ (((p2 ∨ p4) ∧ p5) → p1)))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205231558554200863500339082405 : ((((p2 → p1) ∧ p3) ∨ (p4 ∨ p1)) ∨ (((True ∨ ((p4 ∧ (p3 ∨ p3)) ∨ ((False ∨ p2) → p3))) → (False ∧ ((p3 → True) → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46811010282222151240183755896 : ((((((p3 ∨ (((True ∧ False) ∧ p2) → p4)) → (False ∧ ((p5 → False) ∧ ((p1 → p1) → (p2 → p3))))) ∨ p5) ∧ p4) ∨ (p3 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180426939013530190213938456741 : (((((((p3 → True) → (False ∧ p4)) ∨ p5) ∨ False) → False) → (p4 ∨ p2)) → (((p4 ∨ (p4 → p1)) ∨ (p4 → (p4 ∨ p1))) ∨ (False ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702301894709027668070999385346 : (((((p3 ∨ ((p3 ∧ ((p5 ∨ p2) → False)) → p2)) ∧ p1) ∨ (((p5 ∧ False) ∧ (p2 → (True ∧ True))) → ((p2 → p1) ∧ (True ∨ p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618537905923607774852391205275 : (((((True ∧ ((False ∨ p3) → p1)) → (p5 → (False ∨ ((p4 → (p2 ∧ (((p3 ∧ p4) → ((p3 ∧ p1) ∧ p5)) ∧ False))) ∨ True)))) ∨ p5) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65466316854748606027705236959 : ((p3 ∨ (True ∧ (((p5 ∨ (p1 ∧ (p2 → p3))) ∧ p1) → ((((p5 ∧ False) ∨ (p4 ∨ p1)) ∨ ((p5 ∧ p2) → (p4 ∧ p2))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167135237440268115193850610425 : (((((p3 ∨ ((True ∨ p5) ∨ p1)) ∨ p5) ∨ (False ∧ (p1 → (False ∧ (p1 ∨ True))))) ∨ p4) → ((((p2 ∧ (p3 → True)) → False) ∧ p5) ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h6 =>
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
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256205807076732441707594788035 : ((False ∨ True) → (p5 → (p5 ∧ (p5 → (((p1 ∨ (p1 → True)) → ((False ∧ (p1 ∧ (p2 → p2))) ∨ p4)) ∨ (p5 ∧ (p4 ∨ (p3 ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135204709517048971392879183191 : ((((p2 → ((p3 → p3) → ((((p2 ∨ (p4 → True)) ∧ (p5 ∧ p1)) ∧ False) ∧ True))) ∨ (p1 ∧ True)) → (p3 → p4)) ∨ (True ∧ (p2 ∨ True))) := by
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
theorem thm_5_vars_165281672129799114032721141964 : ((((False ∨ (((p3 → p3) ∧ p2) ∧ ((p5 → p5) ∧ p4))) → (p1 ∨ p4)) → (p2 ∧ p5)) ∨ (True → (p3 → (p1 → (p2 → (p3 ∨ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671954938031060536676356011360 : ((((((((((((False → p2) ∨ p2) ∨ p4) ∨ p1) → ((p4 → (False ∨ p3)) ∨ True)) ∧ p1) → p4) ∨ p4) ∨ p4) → ((p2 ∧ p4) → p2)) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157879487017878581156535545383 : (((((False → (p1 ∨ p3)) → p3) ∨ (p5 ∨ (False ∧ False))) ∨ (True → (True ∨ (p2 → (True ∨ p3))))) ∨ ((((p3 ∨ False) → p1) → p2) → p3)) := by
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
theorem thm_5_vars_231399253479165133062213872953 : (((p1 → p1) ∨ False) → ((p3 ∨ p5) → (((((p1 ∨ p1) ∧ p5) ∨ (p5 → p5)) ∨ (p4 → (p5 → p4))) ∨ (False → (False → (p3 → p5)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173621370421262151318544327266 : (((p5 ∨ ((((p5 → p1) → True) → ((p2 → (True ∧ p5)) → p4)) → p1)) ∧ True) → (((p3 → p5) ∧ ((True ∨ p5) ∧ (True → True))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136860707378659831611613105130 : (((p5 ∧ p3) ∨ (((p5 ∨ p1) ∨ p3) ∨ (p4 → (((p1 ∧ (p4 ∧ (((p5 ∨ False) ∧ p5) ∧ p3))) ∧ p1) → p3)))) ∨ ((p3 → p3) ∧ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350917821072018410954817446945 : (p4 → (((((((False ∧ p5) ∧ p3) ∨ (p2 ∧ True)) → ((((p5 ∧ p4) ∧ (p1 → p4)) ∧ False) ∨ True)) → (False ∧ p4)) ∨ p2) ∨ (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229355964307540968600907777993 : ((p1 → (p1 ∧ p5)) ∨ ((((p5 ∨ (p1 ∨ ((p4 ∧ p4) → p2))) → (((p3 → (False → p3)) ∧ ((p5 → p3) ∧ p2)) ∨ p5)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208531883149265663353124404607 : (((True ∨ p3) → (True → (p5 ∧ False))) → ((((p2 → p3) ∧ p4) ∧ (p5 ∨ ((True ∨ (False → True)) ∧ p4))) → ((p3 ∨ (p1 ∨ p3)) ∨ p2))) := by
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
  cases h4
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h23 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h24 := h1 h23
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h26 := h24 h25
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50075236902081994977795628459 : ((((p5 → p5) → (((((p5 ∧ p4) → p2) ∧ p1) → (False ∧ p3)) ∨ ((p2 ∨ p3) ∧ (p1 ∧ p5)))) ∧ (((False → p4) → p5) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49612002207518002799729265608 : ((((((p4 → p3) ∨ (p3 ∧ p5)) → (p5 ∨ p3)) ∧ (True → (p5 ∨ (True ∨ (p1 → ((False ∧ p2) ∨ True)))))) → (False ∧ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230341233870694671413156221001 : (((p2 ∨ p2) ∧ True) → ((p1 ∨ (False ∧ p5)) ∨ (((((p2 ∧ (True ∨ True)) ∧ (True ∧ p3)) ∧ (p1 → p3)) ∧ ((False → p5) → p3)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347262000927200505450506146935 : (p3 → (((True → False) → (p4 → (((False ∧ p2) ∨ p1) ∨ p4))) ∧ ((p3 ∨ p3) ∧ (p5 ∨ (((((False ∨ False) → p4) → False) ∨ False) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157994904612329070078315161929 : ((((p5 → p1) ∧ ((p1 ∨ p5) ∨ (p2 ∨ p4))) → ((p2 ∨ p2) → ((p2 → p1) ∧ (True ∧ True)))) ∨ ((p5 ∨ True) ∨ ((False ∧ p1) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348267734453849476191227965851 : (p3 → (True ∧ (((((True ∨ p2) ∨ True) ∧ p1) ∧ p2) ∨ ((p1 ∨ (((p3 ∧ p2) ∨ ((p4 ∧ False) ∧ ((False → p3) ∨ False))) ∨ True)) ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753525179569318063434555105623 : (((False ∧ (((p5 → (p2 → (p3 ∨ (((p3 ∨ (p4 → True)) ∨ p4) ∧ ((p2 → p3) ∨ False))))) ∨ p4) ∨ (p4 → (p1 ∨ (False → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134904986598619743249722223601 : (((((p4 ∧ ((False ∧ p1) ∧ (p4 ∨ p3))) ∧ (True ∨ (((p4 → (True → True)) ∧ True) ∨ p1))) ∧ p4) ∧ (True → p2)) ∨ ((True ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190914372749139091723930871066 : (((p5 → (False → (p5 → (True ∨ True)))) → (p2 ∨ p2)) ∨ ((p5 ∨ ((((p5 ∨ True) ∧ ((p1 ∧ p5) → p5)) ∨ p3) → False)) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48688629374364580062781483591 : ((((((False ∧ ((p2 → False) → p1)) ∨ p4) ∧ True) ∨ (p4 ∨ ((p5 ∨ (p4 → (p2 ∨ p5))) ∨ (True ∧ True)))) ∧ (False → (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170016200749403138434794595725 : (((((((p3 ∨ p4) ∨ (p4 ∨ False)) ∨ p3) ∧ p1) → False) ∨ (False → (False → True))) ∧ (p3 → (((p5 ∧ p3) ∧ p1) ∨ ((False ∨ p4) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206413770894743796272284973913 : ((p3 ∨ (p3 ∧ (p1 ∨ (False ∨ p4)))) ∨ (((p2 ∨ (((p1 ∧ (p4 ∧ p5)) ∧ p5) ∧ (p3 ∨ ((p1 ∨ (p4 ∨ True)) ∨ True)))) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299456328563626247838320442282 : (False ∨ ((p4 ∨ (((False → ((p5 → (p2 ∧ ((((True ∧ (False ∧ p1)) → p5) → p5) → p2))) → (p4 ∨ True))) → (p2 ∨ p3)) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166232113798547515785149030970 : ((p2 ∧ ((False ∧ p4) ∨ ((((p2 ∧ ((p1 ∨ p5) ∧ (p2 → False))) ∨ False) ∧ p2) ∧ p1))) ∨ (((False ∧ p3) ∧ ((p4 → False) ∧ p1)) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41192806869137423546132388756 : (((((p4 ∧ (p4 → False)) ∧ (True ∧ (p2 ∨ (((p5 ∧ p4) ∧ ((p5 → p2) ∧ False)) → (True → p3))))) → ((True ∨ p3) ∧ p2)) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h11.left
  let h15 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h18 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h19 := h13 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673674831987600371210324273140 : (((((p3 → (p3 ∨ p2)) → (((p2 ∨ ((((((p2 ∨ p3) ∨ p4) ∨ p5) ∨ False) ∧ p1) ∨ p4)) ∧ p2) ∨ True)) → (p2 ∧ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60834346034139678603669540348 : ((True ∧ (False ∨ ((((((p1 → True) ∨ p4) ∨ (p3 ∧ p5)) → (((p5 ∧ p3) ∧ p5) ∨ p3)) → p1) ∨ (False ∨ ((p1 ∧ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668466723721916433483173742220 : ((((((((p1 ∧ p5) ∧ p3) ∨ ((p5 ∧ (p3 ∨ (((p2 ∨ p4) → p3) ∨ False))) → True)) ∧ (p4 ∨ p2)) ∧ p4) ∨ (True ∨ (p1 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171159357560019249562875354792 : ((p1 → (((p5 ∧ p3) ∧ p4) ∨ ((p3 ∧ ((False ∧ (p4 ∨ p4)) ∧ p5)) ∨ p1))) ∧ ((p4 ∧ p3) → (p2 ∨ (p4 ∨ (p2 ∨ (p1 ∧ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168327919126976419433431777778 : (((p3 → p5) ∧ ((((((p3 ∨ False) → p1) → False) ∧ (True ∧ (False → p3))) ∨ p5) ∧ p4)) → (p5 ∨ ((((p5 → p1) ∨ p4) ∧ p4) ∧ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58913356353351042638066882845 : (((p1 ∧ False) ∨ (((p4 ∧ ((True ∧ p2) ∧ (((True ∨ True) ∧ p4) ∨ (p5 ∨ (p1 → False))))) ∨ (True ∨ p5)) → (p1 ∨ (p5 → True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- True on the right can always be proven directly.
      apply True.intro



