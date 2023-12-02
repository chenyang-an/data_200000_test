variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705409550624261024105089583519 : (((((p1 ∧ (p4 → ((p2 → False) → p5))) ∨ False) ∧ ((((((False ∧ True) ∨ False) ∨ (((p2 ∨ p1) → p3) ∧ p2)) ∧ p4) → p1) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323986003792358919585588516781 : (p5 ∨ ((((((p3 ∨ False) ∧ (p2 ∧ (p3 ∨ True))) ∧ p3) → (p3 ∨ p5)) → p2) ∨ ((p4 ∨ True) ∨ (p2 ∨ ((p2 ∧ p3) ∧ (True ∧ p5)))))) := by
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
theorem thm_5_vars_133951079393835233814626483167 : (((p2 → ((p4 ∨ (((True ∧ (p4 ∧ p3)) ∨ p5) ∨ p2)) ∨ (True ∧ ((p2 ∨ p1) ∧ ((p5 ∧ p2) → p4))))) ∧ p4) ∨ (True → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338609832334462832669183620739 : (p1 → ((p4 ∧ (False → p3)) → (((((p1 → True) ∨ p4) ∧ (False ∨ (((p3 ∨ p5) ∨ False) → False))) → p3) ∨ (False ∨ ((p5 ∨ p5) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39665903092781451958891295086 : (((p3 ∨ (p3 → (((p3 ∧ (((((p5 ∨ (p5 ∧ p3)) → (p5 ∧ p1)) → ((p5 ∨ False) ∨ p2)) → p4) → p5)) ∨ p4) ∨ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207496881184236474293689217384 : (((p5 → ((p4 ∧ p3) ∧ p1)) ∨ True) → ((((((True → p3) ∨ True) ∨ p3) → p2) ∨ True) ∨ ((p5 → (p4 → ((p5 ∧ True) → p5))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689575316431497129858248209864 : ((((((p1 ∧ (p3 ∧ (p1 ∨ p5))) ∨ p5) ∧ (p2 ∧ (((p3 ∧ p1) ∧ p3) ∨ p2))) ∨ ((p5 → p5) ∨ ((p2 ∧ True) → (True → p5)))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909920342802178947236621378454 : ((((True → ((((p4 ∧ p3) ∨ True) ∨ False) ∧ (False ∧ (False ∨ (False → (True → (p4 → p3))))))) ∧ (((p2 → True) ∨ (p5 ∧ p1)) ∨ p3)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41466539901852910477032821773 : ((((p2 → (p1 ∧ (p3 ∧ ((p3 ∧ (p4 → p4)) ∧ (p5 → p3))))) ∧ ((((((p4 → p1) ∧ p1) ∨ p4) → False) ∧ p3) ∧ p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66323431044528910345143253126 : ((p5 ∨ (False ∧ (p3 ∧ (((p4 ∧ p5) → p5) → ((p5 → (p3 → (((p4 ∧ False) ∧ False) ∧ (True ∨ True)))) ∨ ((p1 → False) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172020438948157642559717824586 : (((((p3 ∨ p2) ∨ p1) ∨ (((False ∨ p1) ∨ p4) ∧ (p3 ∨ p5))) ∨ (True → p2)) ∨ (((p5 → p2) → p4) ∨ ((False ∨ True) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_47189818151758234179102480785 : ((((p3 → (True → ((p3 ∧ (p4 ∨ ((p2 ∨ False) → p3))) ∧ p4))) ∧ (p2 ∨ (((p1 ∨ p1) → False) ∨ (False ∧ p4)))) ∨ (True ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790516432698588793251717164908 : (((p5 ∨ (p1 ∨ (((p2 → (p2 ∧ ((True ∧ (False ∧ (((p2 ∨ p1) ∧ p1) ∧ p4))) ∨ ((p5 ∧ True) ∨ p2)))) ∧ (p4 → p4)) ∨ False))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149605577226291991211580323097 : ((p3 ∧ (((p2 ∧ p3) ∧ p1) ∧ (((True ∨ True) ∧ (True → (p3 → (p2 → (p4 ∧ (False ∧ p4)))))) ∨ p3))) ∨ ((p5 → p5) ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205816057469522883554900325277 : (((p4 ∨ p4) → ((p1 ∨ p2) ∧ p2)) ∨ (p4 → (False → ((((p2 ∨ p5) ∧ p2) ∧ p2) ∧ ((False ∧ ((p2 ∨ (p4 ∨ p5)) → False)) → p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172561444874644132606902977702 : (((p3 ∧ (p2 ∨ p2)) ∨ ((((p3 ∨ False) ∧ (False ∨ False)) ∧ (p5 ∨ p2)) ∧ False)) ∨ (True ∨ ((p1 ∧ (p3 ∧ False)) → ((p1 → p2) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164661192583964355118299758753 : (((p3 → (p1 → (((p5 ∧ p3) → ((p2 ∨ (p4 ∨ (p4 ∧ p1))) ∧ True)) → p4))) ∧ p5) ∨ ((True → False) ∨ ((p3 ∨ (p3 ∨ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205938019026832029369474949312 : ((False ∧ ((p4 ∨ p4) ∨ (p2 ∧ p4))) ∨ (((p1 ∧ (True → p5)) → ((True ∨ ((p3 ∧ True) → (p2 ∧ p5))) → (p4 → (p3 ∨ p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249655292797627970962818759234 : ((p5 ∨ p4) ∨ (((((((False ∧ ((p3 ∨ p4) ∨ p1)) → True) ∨ (True ∧ p4)) ∧ p4) → p1) ∨ (True ∨ (p2 → ((p4 ∧ p2) → p4)))) ∨ p3)) := by
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
theorem thm_5_vars_339969931495020808730896913689 : (p1 → (p1 → ((p5 ∧ (((p4 → p3) ∧ ((((p3 ∨ p4) ∧ p3) ∧ p3) ∨ (p5 → (p2 → ((p5 ∨ True) ∨ False))))) → (p5 ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613521406889288107170344109117 : (((((p5 → (p4 → ((p2 ∧ True) ∨ (((((True → (p4 → (False ∧ True))) ∨ p5) ∨ p3) ∧ (p1 ∨ p5)) ∨ p2)))) → (p4 → p2)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_116817676829138594160105493764 : (((p4 ∨ p2) ∨ ((p3 ∨ (True ∧ (False ∧ ((False ∨ ((p1 ∨ (True → True)) ∨ p1)) → (True ∧ ((p3 ∧ p5) ∧ p4)))))) ∨ p3)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299269399999299251044098759527 : (False ∨ ((((p2 ∧ (p1 ∨ ((p1 → True) ∨ ((p5 → p3) ∧ p4)))) ∨ (p4 ∧ (p5 ∨ True))) ∨ (p4 ∨ (p4 → (p4 → (p1 → p1))))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190675509564461694139427058064 : (((p2 → (p4 ∧ ((p2 ∧ p2) ∧ (True → p4)))) → p4) ∨ (((p5 → (p4 ∧ (True → (p1 → p2)))) → ((True → p5) → p5)) ∨ (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52310246175268398029485798214 : ((((p5 → ((p1 → p5) → ((p4 ∧ (True ∨ (p4 ∧ p5))) ∨ p4))) ∧ p4) ∧ (True → ((p2 → (p1 ∨ (p1 ∧ False))) → (p2 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606062413451820028677696913071 : ((((p5 → (p5 ∧ (((p3 ∧ p3) → p2) → ((((p5 → True) → (True ∧ False)) ∧ p3) ∧ (p1 ∨ (((True → p3) ∨ p3) ∧ p1)))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615058524064803481281670331014 : (((((p2 ∨ ((p3 ∧ ((p4 → p3) ∨ (p1 ∧ (p5 → ((p1 ∧ (p5 → p3)) → p4))))) ∧ p5)) → (p3 → (True → (p1 ∨ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_598070380828389568054702691483 : (((((p2 → (p2 ∧ True)) ∧ ((False ∧ ((p4 ∨ (p5 ∨ True)) ∧ (True → (((False → p4) ∧ ((p2 → p4) → False)) ∧ p3)))) ∧ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308599502061954327019027852235 : (p2 ∨ (((p1 ∨ (p1 → False)) → ((p2 ∧ False) ∧ (p1 ∧ ((p1 → ((p5 ∨ p3) → ((p2 → (False ∨ p3)) ∧ (p3 ∧ p4)))) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60714871801403276641115131314 : ((True ∧ ((((p1 ∧ False) ∧ (False → p5)) ∧ p5) ∨ ((p3 ∧ ((((p5 ∧ p2) ∧ ((False → (p2 ∨ p2)) → p5)) ∨ p2) → p1)) ∨ True))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67875834311769802582634661725 : ((p2 → ((p3 ∨ ((p5 ∧ (((((p2 ∧ (p2 → False)) ∧ p2) → p1) ∨ (p5 ∨ p1)) → (p4 → False))) → p4)) → (True ∧ (p2 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42677403914118130809027641575 : (((p4 ∨ (p3 ∨ ((((p5 ∨ ((p5 → ((p3 ∨ (p3 ∨ p3)) ∧ ((p2 ∨ p4) → p4))) ∧ p2)) ∨ True) → (True ∧ False)) → p2))) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((p5 → ((p3 ∨ (p3 ∨ p3)) ∧ ((p2 ∨ p4) → p4))) ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218285179892504180044534151374 : (((p3 ∨ p1) ∨ (p2 → p2)) → (((p2 → (False ∧ (p4 ∧ (False → True)))) ∨ (p5 → p4)) → ((((False → p3) → False) ∧ False) ∨ (p4 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41392310313655247304540506662 : (((((p5 ∨ (p5 → p1)) ∧ (False ∧ (p5 → (((p2 ∧ p1) ∧ p5) → True)))) ∧ (((False ∨ ((p5 → p1) → p1)) ∧ p1) ∧ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71107756160374084550140032719 : (((((False ∨ (True ∨ p1)) ∨ p1) ∧ ((False → (p5 → (True ∧ (p4 → p1)))) → ((False → p1) ∧ (False ∧ ((False → p3) ∧ p4))))) ∧ True) → False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : (False → (p5 → (True ∧ (p4 → p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h11
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h10
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : (False → (p5 → (True ∧ (p4 → p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h19
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h18
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- We need to get the left conjuct of h23 based on <expert-advice>.
        let h24 := h23.left
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h26 : (False → (p5 → (True ∧ (p4 → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- Implications on the right can always be decomposed.
      intro h28
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h27
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h30 := h5 h26
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- We need to get the left conjuct of h31 based on <expert-advice>.
    let h32 := h31.left
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51457880168807724107925745552 : (((((((p2 ∨ p1) ∨ (True ∧ (p4 ∨ True))) ∨ p1) ∨ p4) ∧ (p2 ∨ (True ∧ (p5 → p3)))) → ((p5 → (p4 ∨ (True ∧ True))) ∨ p3)) ∨ p4) := by
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
          cases h3
          case inl h8 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h9
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h13
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h20
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h26
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h30
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h33
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h37
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h39 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h40
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h44
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h46 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h47
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h45
    case inr h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h51
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159909304914579152133924821940 : ((((p4 ∨ (((((False → p4) ∨ (p5 → (p1 → (False → p2)))) ∨ p3) ∧ False) → True)) ∨ False) → False) → ((p1 → ((False ∨ False) ∧ p5)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ (((((False → p4) ∨ (p5 → (p1 → (False → p2)))) ∨ p3) ∧ False) → True)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ (((((False → p4) ∨ (p5 → (p1 → (False → p2)))) ∨ p3) ∧ False) → True)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∨ (((((False → p4) ∨ (p5 → (p1 → (False → p2)))) ∨ p3) ∧ False) → True)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65649444842181475152708438496 : ((p4 ∨ ((True ∧ (p3 ∨ (p2 ∨ (((p4 ∧ (p4 → ((((p3 → (p5 ∨ p2)) ∨ False) → p2) ∨ p4))) → (p5 ∧ p1)) ∧ p4)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_973098556704980511297225656951 : ((((p3 ∨ True) → ((((p5 → (p1 ∨ ((p4 ∧ (False → (((True ∧ p5) ∨ (p1 → p4)) ∨ p4))) ∨ p5))) → False) ∨ (p2 ∧ False)) ∧ True)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → (p1 ∨ ((p4 ∧ (False → (((True ∧ p5) ∨ (p1 → p4)) ∨ p4))) ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752780240158556693118855208060 : (((False ∧ ((False ∧ (p2 → (((p4 → (False ∨ ((p1 ∨ (False ∧ p4)) ∨ p4))) ∨ (((p3 ∨ False) ∧ False) → p5)) ∧ (p5 → p2)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135534843502750349221765333888 : ((((((((False ∧ (p5 ∧ False)) ∧ False) → True) ∨ (True → p3)) → True) → (False ∧ False)) ∧ ((p5 ∨ (p4 → p5)) ∨ p2)) ∨ (p4 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766831982050696817553727175628 : (((p4 ∧ (p4 ∨ (((p3 ∧ ((((p2 ∧ p5) ∧ (((p2 ∧ p2) ∨ ((p5 ∧ p5) → (p1 ∨ p5))) ∧ p4)) ∧ p1) → p1)) → True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165225791640282111122036362472 : (((((False ∨ p1) ∧ p5) ∧ ((p5 ∧ (p3 → p4)) ∨ ((p1 ∨ p5) → p5))) ∨ (p4 ∨ p2)) ∨ ((p2 → True) → (((p2 ∧ p3) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791603277838180559866213403766 : (((True → ((((p5 ∨ p1) ∧ ((((True ∧ p3) ∨ (p4 ∨ ((False ∧ (p4 ∧ (p4 ∧ p2))) ∨ (False → p1)))) → p3) → p3)) → p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54053489309192441955052069561 : ((((p5 → (p2 ∨ (p3 → p4))) ∨ (False ∧ (p2 → False))) → (False ∧ (((p1 ∧ p5) ∧ ((((p2 → False) ∨ True) → p3) ∧ p3)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50909011377304388863525849996 : (((((False → (False → (p5 ∧ ((False ∨ p5) ∨ p2)))) ∧ ((p2 ∧ p2) ∨ p2)) ∨ (p1 ∨ True)) ∧ (p4 ∨ (p3 ∨ (True ∨ (True ∧ False))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63181052512573198459872836920 : ((p5 ∧ ((p1 → (((p1 → True) ∧ (p5 → (p4 → ((p1 ∨ ((p2 ∧ ((p4 ∨ False) ∨ False)) ∨ p2)) ∧ p3)))) ∧ p2)) → (p1 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55741236311340161406750560285 : ((((False ∧ (p1 → p1)) → p5) ∧ ((p5 ∨ ((((p5 → p4) → False) ∧ ((((p3 ∨ (p1 ∧ p3)) ∨ p1) ∧ p2) ∨ True)) → p2)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136592832979322465934262604722 : (((p1 ∨ (p5 ∧ False)) ∨ ((True ∧ p2) ∨ (p1 ∨ ((p4 ∧ (((p2 ∧ p2) ∧ (p4 ∧ (True ∨ p4))) → p1)) → p3)))) ∨ ((p1 ∧ False) → p2)) := by
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
theorem thm_5_vars_308635830074089839781386782191 : (p2 ∨ ((True ∧ (((False ∧ (((p1 ∧ (((p1 → (False → p4)) ∨ p1) ∧ p2)) ∧ (p4 → p4)) ∧ (p3 → p1))) ∨ p5) ∧ (p2 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48769941392023214099970799902 : ((((p1 → p2) ∨ ((True → True) ∧ (((p4 → p3) → (((p1 → p1) ∨ True) ∧ p3)) → ((p4 ∧ True) ∨ p2)))) ∧ (p4 → (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613316925417496588221580552612 : (((((((True ∧ p1) ∧ p5) → (p3 ∧ (True ∨ (((p2 → p3) ∧ (p5 ∨ (p5 ∧ False))) ∨ ((p5 → True) ∧ p2))))) → (False ∨ p2)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47618278572826842602314615255 : (((p5 → ((True ∨ (((((p1 ∧ p4) ∨ ((p4 → p5) ∧ False)) ∧ (p5 ∨ p4)) → (p4 ∨ (True ∨ p4))) ∧ p4)) → p1)) ∨ (False → False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709780081401922319830800927497 : ((((p1 → (p4 → ((p1 ∧ p2) ∨ (p4 ∧ p3)))) → (p1 ∧ (((True ∧ (p1 → p2)) ∨ ((True → ((p3 ∨ p2) ∧ p3)) ∧ False)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219773501491897324172240721448 : ((p2 → ((p1 ∨ p1) → p1)) → (p4 → ((p3 ∧ (((p4 ∨ ((True ∧ False) → True)) ∨ (False ∨ p1)) → p2)) ∨ (False → ((p1 ∧ True) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603399277328345581510829877006 : ((((p3 ∨ ((((False ∨ p1) ∧ ((p1 ∧ p2) → False)) ∧ (p5 ∧ ((False → (p1 ∨ (True ∧ (p4 ∨ p2)))) ∧ (p5 → p3)))) ∨ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909757978423409752684177478670 : ((((False ∨ ((p1 → (((p2 → ((True ∧ (p5 → True)) ∧ p5)) ∨ (p5 → p5)) ∧ False)) ∧ p1)) ∧ (False ∨ (False → ((p1 ∨ p5) → p1)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762371168194653329661412600985 : (((p3 ∧ ((p5 → ((((p5 → (p3 → (p3 ∧ (p4 ∨ (p1 ∨ p5))))) → p1) ∨ (p2 → (p4 ∨ p2))) ∨ p1)) ∨ ((False ∧ p5) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320309736756867340143548602087 : (p4 ∨ ((False ∨ p5) ∨ (((((p4 → (p5 ∨ (p3 ∧ (p4 ∨ p3)))) ∨ True) → (False ∧ False)) ∧ ((p2 ∨ False) ∧ ((p5 ∨ p5) → True))) → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 → (p5 ∨ (p3 ∧ (p4 ∨ p3)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178434108061870623770859585215 : (((((p2 ∧ (p3 ∧ False)) ∧ (p2 ∨ True)) ∨ False) ∧ (False → (True ∨ p5))) ∨ ((p4 → (True ∨ (False → p2))) ∨ ((p2 ∨ (p5 → p4)) ∨ p2))) := by
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
theorem thm_5_vars_740776353374230254170434694125 : ((((p2 ∨ p5) ∨ (p2 ∨ ((((p1 ∧ (False ∧ (p4 ∧ ((p3 ∨ p1) ∨ p5)))) → p5) → p3) ∨ ((True ∧ (False ∧ (p1 ∧ p1))) → True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324153879725481450660223790956 : (p5 ∨ ((True → (True → (p4 → (False → (False ∨ (False → True)))))) ∧ (p1 ∨ (False ∨ ((p3 → p5) → (((p3 ∧ p2) ∨ p3) ∨ (False → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153225028607136938455084331134 : ((True ∨ (p1 ∧ ((((p1 → (p4 ∨ p3)) → ((p3 ∨ p1) ∨ (p3 ∨ (False → p2)))) → p5) ∧ (p2 → p2)))) → (((True → False) ∧ True) → p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336072030385722907990086154978 : (p1 → ((((p3 ∧ ((p1 ∨ (p2 ∨ p1)) → (((p1 ∨ (True ∧ (False → ((p2 → p5) → p3)))) → (p5 → p5)) → p2))) ∨ False) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179425338622311235591846319331 : ((p4 ∨ (((p2 ∨ p2) ∨ p4) ∨ ((((p4 → p4) → p2) → p1) ∨ p4))) ∨ ((((p1 ∨ p2) ∨ p4) ∧ p2) → (((p4 ∨ p1) → p2) ∨ True))) := by
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193531180628481733350549926666 : (((p5 → p2) ∨ (p1 ∨ ((False → p4) ∨ (p2 ∨ False)))) → ((((p1 ∧ False) ∨ True) ∨ (p3 ∨ p3)) ∨ ((p5 → (p1 ∧ p5)) ∧ (False → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167169489119769091061925526925 : ((((p5 → p5) ∧ ((p2 ∧ ((p3 ∧ p4) → ((p1 ∧ p4) → p5))) ∨ (p3 ∨ True))) ∨ True) → ((p5 ∨ ((p1 ∨ (p1 ∧ p4)) → p5)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342085429139387368084129129769 : (p2 → ((True → (((((p5 ∨ False) ∨ p2) ∧ (((True ∧ p5) → p3) → (p4 ∧ True))) → (p3 ∧ p5)) ∧ (p5 → p4))) → ((False ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617704268534263472294105885043 : ((((((p5 → (p4 → p5)) → (p1 ∧ p4)) ∨ (p3 ∧ (p3 ∧ ((p1 ∨ (True ∧ p1)) ∨ (p3 ∨ (False ∨ ((p1 ∧ p5) ∧ False))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627713383842797814114424186007 : (((((((p3 ∨ (p1 ∨ p2)) ∧ ((((p3 → p1) ∨ (False ∨ False)) → ((p2 → p1) ∧ p5)) ∨ p4)) → ((p1 ∨ False) → True)) ∧ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263495437598365988244827673990 : (True ∧ ((p1 → (((False ∨ p4) ∨ ((((p5 ∨ p4) ∨ p3) ∨ (p2 → (p1 → (p1 ∨ p3)))) ∨ p1)) ∨ (p4 ∧ True))) → ((True → False) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300359095429603078450475490318 : (False ∨ ((((p1 → (False ∧ ((p2 ∨ (True → p1)) ∧ (((p2 ∨ p4) ∨ p4) ∧ (p4 → (p4 ∧ p5)))))) ∨ True) ∨ True) ∨ ((True ∧ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671056364125835376773386214395 : ((((False ∨ ((((((p2 ∨ p4) → (((False → p5) → p2) ∧ p1)) ∨ ((True ∧ False) → True)) ∨ p2) ∧ p2) → p5)) ∨ (False ∨ (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114040686127897096732701665995 : (((((p5 ∨ False) → ((((p3 ∨ (True ∨ p3)) → p1) ∨ p2) → (p4 ∨ (p2 ∧ True)))) ∧ (p5 ∨ False)) ∨ ((p5 → p5) ∨ p4)) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39188746929688454469979029541 : ((((p4 → False) → (p1 → ((((True ∨ p4) ∨ p5) → ((p4 ∧ p1) ∨ ((p5 → p4) ∨ ((p2 ∨ False) ∨ p5)))) ∨ (True ∨ p1)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318775450310459387365062321509 : (p4 ∨ ((p4 → (((True → p3) ∨ (((p1 ∨ p2) → True) → p1)) → ((((p1 → (p1 → False)) ∨ p1) → (p4 ∧ p1)) ∧ p1))) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178703721519379589783100889071 : (((p1 ∧ (p5 ∨ (p5 ∧ p1))) ∨ (p2 ∨ ((p4 ∨ p1) → (p1 ∨ True)))) ∨ ((((p5 ∨ (((p1 → p1) ∨ p2) → p3)) ∨ p3) → False) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113003663230060587370351369204 : (((p4 ∧ (((p1 ∨ (((True → (p1 → ((True ∨ p5) ∧ p4))) ∨ (True ∨ False)) ∧ p2)) ∧ p5) → ((p2 ∧ p5) → p4))) → p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324815480184629755427954758859 : (p5 ∨ ((p1 ∨ True) ∧ ((((True ∨ p3) → (((p4 ∧ p5) ∧ (False ∧ ((((p3 → p2) ∧ False) ∨ p4) ∧ p3))) ∧ (False ∧ False))) ∨ False) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173224308857228286584151363089 : ((p5 ∨ (p5 → (((p4 ∧ p2) ∨ (False ∨ p5)) ∧ ((p1 ∨ True) → (True → p3))))) ∨ (((p5 ∨ ((p1 ∧ p4) ∧ p4)) → p4) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339662730338676362725310019764 : (p1 → (p3 ∨ (((p2 ∨ (((((p4 ∧ (p5 ∧ p1)) ∧ True) ∧ p3) ∨ ((p3 → (p4 → (p1 ∧ (True ∧ p3)))) ∧ p2)) ∧ p5)) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263416419506794011694784772987 : (True ∧ ((False ∧ (p1 ∨ (False ∧ (p2 → ((((p5 ∨ (p2 → True)) ∧ (False → (p2 → p2))) ∧ p5) ∧ (p5 → False)))))) ∨ (True ∨ (p4 ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184473281117371518376466242005 : ((((((False ∨ (p3 ∨ p5)) ∨ p5) ∨ False) ∨ p1) ∨ (p2 ∧ True)) ∨ ((((p5 ∧ (p3 → p2)) ∨ p4) → (p5 ∨ ((p2 ∨ True) ∨ False))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68590817495777256245350542142 : ((p4 → ((p2 ∨ (((((p3 → (False ∧ p2)) ∨ p1) ∧ (((p4 → False) ∨ (p2 → False)) ∧ p5)) ∨ p4) ∧ ((p1 ∨ False) ∨ p5))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158982703807433236445255128963 : ((p3 ∨ (((((True ∧ True) ∧ (p1 → p3)) ∧ p4) ∧ True) ∨ (((p5 ∨ (p2 → p5)) → p2) ∨ p2))) ∨ (((p4 ∧ True) ∨ (False ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_701778378098669520245835358211 : ((((p2 ∧ (((False → (p2 ∧ False)) ∨ p3) → (p1 ∧ p4))) ∧ (p5 → (p1 → (((False ∧ p1) ∧ ((p3 ∧ (False ∨ p4)) ∨ p5)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64208283882083474798680725500 : ((False ∨ (p2 ∧ (((p3 ∨ p5) ∨ p4) → (True → ((((p3 ∨ (p2 → (True ∧ p3))) ∨ (p5 → p4)) ∧ (p4 → p5)) ∨ (p3 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262225494875124589976525200465 : (True ∧ (((p3 → ((True → p2) ∧ (p5 → (p2 ∧ ((p2 → (p1 ∧ ((p5 ∧ (p5 → False)) ∨ p4))) ∧ (p5 → p3)))))) ∧ (False ∧ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167882078281993167712073824450 : (((p2 ∧ ((p3 → p4) ∧ ((p5 ∧ (p2 ∨ p2)) ∨ False))) → (p3 ∨ (p5 → (p2 → p4)))) → (((True ∧ True) → p3) ∨ (p3 → (False → p2)))) := by
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
theorem thm_5_vars_46729034873297817278558752670 : (((True → ((((p4 → False) → p4) ∨ p1) → ((p1 → False) ∨ (False → ((p4 → ((True ∨ True) ∨ p4)) ∧ (p4 ∨ p5)))))) ∧ (False ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315863015309989964553667511888 : (p3 ∨ ((p4 → False) → (True ∧ ((p4 → p5) → ((((p3 ∧ p1) → (p1 ∧ p5)) ∨ True) ∧ ((p2 ∨ (False → p1)) → (p3 ∨ (True ∨ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_230596277529117780193866446522 : (((p1 → p5) ∧ p2) → (((((((True ∨ p1) → (p5 ∧ p5)) ∨ p4) ∧ False) → (p3 ∧ (p4 ∧ (p4 ∧ ((False ∧ False) ∨ p2))))) → p1) ∨ True)) := by
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
theorem thm_5_vars_336023478299244684947039307149 : (p1 → ((p5 ∨ ((((p3 → (True ∨ p4)) → (True → p5)) ∧ True) → (((p4 ∨ p1) → (p4 ∧ p3)) ∨ ((True ∧ p5) ∧ (False → p1))))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → (True ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216024825901425561869022281212 : ((p5 ∨ ((p5 ∧ p3) ∨ p1)) ∨ (((p2 ∨ (False ∧ (True → False))) → p4) → (((((p1 → False) ∧ (False → p4)) ∧ (p1 ∨ p5)) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103375008535431056517032850338 : (((p1 → (p1 ∧ (p4 ∨ (False ∨ ((p5 ∨ (True ∧ (p4 ∧ ((p5 ∧ p3) ∧ (((True ∧ p3) ∧ False) ∨ p4))))) ∨ p1))))) ∨ p1) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125507316696987679388509986616 : (((p3 ∨ p5) ∧ (((p4 ∧ p4) → ((p5 ∧ ((True → ((p5 ∨ p5) → p2)) ∨ False)) ∨ (p3 ∨ (True ∧ (p3 ∨ False))))) → p1)) → (p1 → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191895623409390178540229749000 : ((p5 ∨ ((((False ∨ (p1 → False)) → p2) ∧ p5) → p3)) ∨ (p4 ∨ (False → (p4 → ((p2 ∨ (False → (False ∨ ((p2 → p1) ∨ p5)))) ∨ p1))))) := by
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
theorem thm_5_vars_207494765792330477303577014769 : (((p4 → (False ∨ (p4 ∨ p4))) ∨ p2) → (((p1 → p5) → (False ∨ (False ∨ False))) ∨ ((p4 ∨ (p5 ∨ (True ∨ ((p3 ∨ False) ∧ p4)))) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_326953947635777053616798884915 : (True → (((((False → (((p3 ∨ True) ∧ p2) → (p1 → p3))) → True) → ((((p2 ∨ p4) → p5) → (False ∧ p2)) ∧ p1)) ∨ (p1 ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909053795060734461805777729927 : (((((True → (False ∨ (((p4 ∨ (p1 ∧ p1)) ∧ p4) ∨ p2))) ∧ (p3 ∨ ((p3 → p5) → p4))) ∧ (((p1 → p4) ∨ False) → (p1 ∧ False))) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h15 : ((p1 → p4) ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h17 := h3 h15
          -- We need to get the right conjuct of h17 based on <expert-advice>.
          let h18 := h17.right
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h22 : ((p1 → p4) ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h23
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h24 := h3 h22
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h29 := h4 h28
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h35 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h36 : ((p1 → p4) ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h37
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h38 := h3 h36
          -- We need to get the right conjuct of h38 based on <expert-advice>.
          let h39 := h38.right
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h43 : ((p1 → p4) ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h44
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h45 := h3 h43
          -- We need to get the right conjuct of h45 based on <expert-advice>.
          let h46 := h45.right
          -- False on the left can always be used.
          apply False.elim h46
      case inr h47 =>
        -- One of the premise coincides with the conclusion.
        exact h47
  -- True on the right can always be proven directly.
  apply True.intro



