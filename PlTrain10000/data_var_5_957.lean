variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119281363705759993721274345162 : ((p3 → (((((p4 ∨ (p5 ∧ ((p2 → (p3 ∧ p1)) → False))) ∨ (p3 ∨ p2)) ∨ ((p5 ∧ False) ∨ (p4 ∧ p5))) ∨ p5) ∨ p2)) ∨ (p5 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264995730834199344065972591386 : (True ∧ ((p1 → p4) → ((True → ((p2 ∨ False) ∧ p4)) → ((p3 → p5) ∨ (p5 → ((((((True → p4) → p5) → p1) ∧ False) → p5) ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299341887721473071390674718239 : (False ∨ (((p1 → (p1 ∧ False)) ∧ (((True ∧ ((False → (p5 → (p4 → True))) ∧ (True → (p4 ∨ (p2 ∧ True))))) ∨ p1) ∧ (p5 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343249006644273301502596750703 : (p2 → ((False → (p5 → p4)) → ((((p2 → (p3 → (True ∧ ((((p2 ∧ p4) → p3) → (True → p4)) ∨ p2)))) ∧ p4) ∧ (p5 → p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209137727045691625909076762182 : ((p3 ∨ (((True → False) → p4) ∨ p2)) → (((((p4 ∧ p4) ∧ False) ∧ p4) ∨ (p4 ∨ (True ∧ True))) ∨ ((True ∧ (False ∧ (True ∧ p2))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_704201622654374972647243256099 : (((((p1 ∨ ((p1 ∨ p1) ∧ (p1 ∧ p4))) ∨ (p3 → True)) → ((p3 ∨ True) → (((p5 ∨ p1) ∧ p4) → (p3 ∧ ((False ∧ p4) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617760826910922529472146392345 : (((((p2 ∨ ((p3 ∧ p4) ∧ (False ∨ p5))) ∨ (False ∨ ((((True ∧ (p5 ∧ p5)) ∧ (p4 ∧ (p4 → p3))) ∨ (False → p4)) → True))) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165943036490903566654990228068 : (((p1 ∨ p1) ∧ ((False ∨ p3) → ((((p3 → p4) ∨ False) ∧ ((True ∨ p3) → p1)) ∧ False))) ∨ (((p4 → (True → (p1 ∧ False))) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171378033918198440852307496605 : ((((p1 ∨ ((False → ((p3 → p5) → p3)) → p3)) ∧ (p4 ∨ (False → True))) ∧ p4) ∨ (((p2 → p3) ∧ ((p1 ∧ p3) ∧ (p2 ∧ True))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301998860615456710471192063744 : (False ∨ ((p5 → True) → (p1 → (((p5 ∨ p3) ∧ (((p5 ∧ (p2 → (p1 ∧ ((p1 ∨ (p2 → p2)) → p1)))) ∧ p2) ∨ p5)) ∨ (p1 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54294161187267313246104379958 : ((((p5 ∨ p4) ∧ (((p3 → p4) ∧ p3) → p5)) ∧ (((p4 ∨ (p2 ∧ False)) ∧ (((p4 ∧ (False ∨ (p2 ∨ p2))) → p2) ∨ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304112241135586749372596322597 : (p1 ∨ ((p2 → (p3 → (p4 ∨ ((True ∨ (p3 ∨ (((p1 ∧ False) → (p2 → (False ∨ ((True ∨ False) ∧ (False ∨ p5))))) → p5))) ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56630203132773824223729172792 : ((((p4 ∧ True) ∧ p3) ∧ (((p5 ∧ p1) ∧ (p3 → ((p4 ∧ (((p5 ∧ p4) ∧ p1) ∧ p5)) ∧ ((True ∨ True) → True)))) → (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57752689856696706328546263748 : ((((p1 → p3) → p1) → (p1 ∨ (p1 ∨ (((p4 ∧ False) ∧ (((p1 ∨ (p3 → p4)) ∨ True) → (p5 → ((p5 ∧ p1) ∧ p3)))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138017196325389754275181776851 : ((True → (((p2 ∧ p2) → (((p3 ∧ (((p2 ∨ p5) → (p3 → True)) ∧ (p2 ∨ p4))) → False) ∧ (p1 ∧ False))) ∨ p1)) ∨ ((p1 → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44248942883692033896130842617 : (((((((p5 → ((p2 ∧ p3) ∨ ((p5 ∨ p1) ∨ (True ∧ (p5 → p4))))) ∨ p2) ∨ p4) ∧ p2) → ((False ∧ (p5 → p1)) ∨ p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65566260193777022394930193349 : ((p3 ∨ (p3 → ((p1 ∨ ((p5 ∨ ((((((p5 ∨ p4) ∨ (p4 ∨ p1)) → p5) ∨ p3) ∨ (p3 ∨ False)) ∨ p4)) ∨ True)) ∨ (p1 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221917995106204982200221394461 : (((p5 ∧ p2) → True) ∧ (p2 ∨ ((p5 ∧ p2) ∨ (((False ∧ (p3 ∨ (True ∧ (False ∧ (p2 ∨ p1))))) ∨ ((False → True) ∨ p3)) ∨ (p4 → False))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137780673414734203329560673603 : ((p2 ∨ (((False ∨ (p4 ∨ p1)) → p4) → ((((p3 ∨ ((p3 ∨ p2) ∧ p3)) ∨ p2) ∨ ((p4 → False) → p1)) ∧ p5))) ∨ (p1 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249168808967684844022967739333 : ((p4 ∨ p3) ∨ (((((p2 ∧ (p3 → (p1 ∨ ((p1 → p5) → ((p5 ∧ ((p2 ∨ True) ∧ p5)) ∨ False))))) ∧ True) ∧ p2) → (False ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192253422758557259770626118253 : (((((p4 ∧ p1) → p3) ∧ (p4 ∨ (p5 ∧ p2))) ∧ p2) → ((p3 ∧ p5) ∨ ((((p5 ∨ p2) ∧ (p5 ∧ p1)) ∨ False) ∨ (False → (False ∧ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60261302355242387096293058547 : (((False → p2) → (((False ∨ (((True → ((((p3 → p5) ∨ p4) ∧ p4) ∧ (False ∧ p3))) ∧ p3) ∧ ((p1 → True) → p1))) ∨ p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345641792515909891029271182496 : (p3 → ((p3 ∧ (((((p2 → p5) → (((p4 ∧ (p4 ∨ False)) ∨ ((p1 → False) ∧ (p2 → p4))) → p3)) → p2) ∨ (p2 → p3)) ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165088630192063785711544997649 : (((p2 ∨ (((((p2 ∨ True) ∧ p3) ∧ p1) ∨ p4) ∧ ((False ∨ (True ∧ True)) → p4))) → p4) ∨ ((p2 ∧ ((p5 ∧ (True ∧ p1)) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208625487649870862901207356849 : ((True ∧ ((p1 ∨ (p1 ∧ p5)) ∨ p3)) → (False ∨ ((((p4 → p5) ∧ (p3 ∧ ((p5 ∨ p4) → ((p4 ∧ p2) ∨ p5)))) ∨ p3) ∨ (True ∨ p5)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663481871000468743897225938890 : (((((p1 → p2) → (p1 ∨ ((p3 → p5) → (p5 ∨ (((((p3 ∧ (p3 → p1)) ∨ True) → (True → False)) → p1) ∨ p2))))) → (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134155597320655948683219319578 : (((((((p4 ∨ False) ∨ (((p1 ∧ False) ∨ p4) → (False ∨ (p5 ∨ False)))) ∨ p5) ∧ p4) → (p2 ∧ (p3 ∨ False))) ∨ True) ∨ (p1 → (p3 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61637633072656251537783774484 : ((p1 ∧ (True ∧ ((p3 ∧ (((p1 → (True → (False ∧ (((p3 ∨ True) ∧ p3) → p4)))) → (p1 ∨ (p3 → (p4 → p3)))) → p5)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8713470866091052402696689474 : ((((p1 → ((False ∧ (False ∧ (True → ((((p2 ∧ p2) → p4) ∧ (p3 → p4)) ∧ (p1 ∧ (True ∨ False)))))) → True)) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46869070703942209995959567081 : ((((p5 ∨ ((p1 ∨ (p2 ∧ (False → (p5 ∨ (p4 ∨ (False → (False ∧ p2))))))) ∧ ((True ∧ (p1 ∨ False)) ∨ p5))) ∧ p2) ∨ (False → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792118469303063734512653118937 : (((True → ((p1 ∧ (p3 ∨ ((((p5 ∨ ((p4 → p4) ∨ True)) → False) ∨ p3) ∨ (True → (p4 ∧ (p3 ∨ p2)))))) ∨ (False ∨ (p5 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65218616727519105981588367059 : ((p3 ∨ (((((True → p1) ∧ p4) ∨ p2) → ((False → p3) → (False ∧ (p1 ∨ (False → (((p5 → (False → p4)) ∨ p5) ∧ p2)))))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160024814283795486405914270965 : ((((True → (False ∧ p3)) → ((p4 ∧ (p2 ∨ (p1 ∧ (True → p2)))) ∧ ((False → p2) ∧ True))) → p3) → (p5 ∨ ((False → p5) ∧ (True → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (False ∧ p3)) → ((p4 ∧ (p2 ∨ (p1 ∧ (True → p2)))) ∧ ((False → p2) ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622226765949639809164803058245 : ((((p2 ∧ (p3 ∨ (((p1 → p3) ∨ (p5 → True)) ∧ (((p4 ∨ ((p3 → (p4 → p2)) → (p1 ∧ (p1 ∨ p4)))) → p2) ∨ p3)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_177875076517340321147874245762 : ((((((p4 → p4) → (((p4 ∨ p2) → False) ∨ p1)) ∨ p4) → p3) ∨ p4) ∨ (p2 → (((p5 → p1) → (((p5 ∧ p4) ∨ True) ∨ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704815180422849531968568680968 : ((((True ∨ (p4 ∧ ((p1 → ((p2 ∨ p1) ∨ p1)) → p5))) → (((((p2 ∨ p2) → (p4 ∧ p3)) ∨ (p3 → p5)) ∨ (True ∨ p5)) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89330361173054881826950136551 : (((p3 ∨ (p1 ∨ False)) ∧ ((p2 ∧ ((p1 ∨ True) ∨ p1)) ∧ (((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) → False))) → p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h11 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h19 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h19
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h30 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
            -- Implications on the right can always be decomposed.
            intro h31
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h32 := h25 h30
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h34 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
            -- Implications on the right can always be decomposed.
            intro h35
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h36 := h25 h34
          -- False on the left can always be used.
          apply False.elim h36
      case inr h37 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h38 : ((((True ∨ (((p3 ∧ p1) → p1) ∨ p5)) ∧ p4) ∧ p1) → True) := by
          -- Implications on the right can always be decomposed.
          intro h39
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h40 := h25 h38
        -- False on the left can always be used.
        apply False.elim h40
    case inr h41 =>
      -- False on the left can always be used.
      apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352798223765287628112739480218 : (p4 → ((p2 ∨ p2) → (((p1 ∧ (p1 ∨ (False ∧ (p4 ∧ p3)))) ∧ p4) ∨ (p1 → (p1 ∧ (p2 ∨ (p3 ∧ ((p3 ∨ p1) → (p4 ∧ True))))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204113479900973230633836727355 : (((((p5 ∨ p2) ∨ True) ∧ p3) ∧ p4) ∨ ((False ∧ p3) ∨ ((p5 ∨ (((p3 ∧ (p2 ∨ p1)) ∧ p4) → p4)) ∨ (((False ∧ p1) → p3) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54967061979249935627081613343 : (((((p3 ∨ p4) ∨ p1) → (p1 → p3)) ∧ (((((p1 → (True ∨ True)) ∧ (False ∨ (p5 ∧ False))) → p2) → ((p1 ∨ p5) → p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149519914154087442435507729931 : ((p1 ∧ (p1 ∧ (((p2 → True) → p3) → ((p2 ∧ (p3 ∧ ((p2 ∨ ((p4 ∧ p4) ∧ p2)) ∧ p2))) ∧ p2)))) ∨ ((p3 → (p5 → p5)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75628446460053717212915068253 : ((((p4 → ((p4 ∨ ((((((p2 ∧ p3) ∨ (False ∨ p5)) ∧ p4) ∨ p3) → p1) ∨ (True → p3))) → (False ∨ (p5 ∨ True)))) ∧ True) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → ((p4 ∨ ((((((p2 ∧ p3) ∨ (False ∨ p5)) ∧ p4) ∨ p3) → p1) ∨ (True → p3))) → (False ∨ (p5 ∨ True)))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307693524060565670871979692056 : (p1 ∨ (p2 → (((p4 ∨ p2) ∨ ((False → p4) → p3)) → ((p1 ∧ ((p2 ∧ False) → (p1 ∨ False))) → ((((True → p4) ∨ True) ∨ p5) ∧ p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
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
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341727255128736378221666384143 : (p2 → ((((p4 ∧ p1) ∧ p5) ∧ (p1 ∧ (((False ∨ (((p4 ∧ ((p4 ∧ (p3 → False)) ∧ p4)) → p1) ∨ p1)) → p5) → p4))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635625480706184996133669628072 : ((((((p4 ∨ True) ∧ ((p3 → (((True ∧ False) ∨ False) → (p1 ∨ ((p5 ∨ p3) ∨ p1)))) → True)) ∨ (p3 ∧ (p3 → (False ∧ True)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232112376377397105789813695666 : (((p5 ∨ p2) → True) → ((((((p2 ∧ False) ∨ ((p3 ∧ p3) ∧ p5)) ∨ p4) → (True ∧ p1)) ∨ True) ∨ (p2 ∧ (((p4 ∨ p5) → p5) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124132797149136447943623151403 : (((p2 ∧ ((((False ∨ p3) ∨ (p1 ∨ True)) ∨ p2) → p1)) ∧ ((p3 ∨ (True ∨ p5)) → ((p1 ∧ ((p2 ∧ True) ∧ p5)) → p2))) → (p3 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∨ p3) ∨ (p1 ∨ True)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350297894412396334366307286366 : (p4 → ((p2 ∨ (((((p5 → (((p1 → (True ∨ (p4 ∨ p3))) → p5) ∨ p1)) → (p1 → ((p3 ∧ False) ∧ False))) ∨ p3) ∧ True) ∧ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727648433078156930842219846 : ((p5 ∨ (((((p4 → p1) ∧ ((p2 → p4) ∧ p2)) ∨ ((p5 ∨ p3) → (False ∨ p4))) ∨ True) ∨ ((False ∧ p5) → (False → p2)))) ∨ (False ∧ p2)) := by
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
theorem thm_5_vars_186989477825340977187378098233 : ((((p2 ∧ p1) ∧ p5) → ((p3 ∨ (p3 ∧ (p2 → False))) ∧ False)) → ((((p5 → p3) ∧ ((True ∨ p2) ∧ (p3 ∧ (p5 → p1)))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137489832385183584196268662107 : ((p5 ∧ ((p2 → (p4 ∨ (((p3 ∨ p3) ∧ p1) ∨ ((((p4 ∧ p4) ∨ (False → (p3 ∧ p1))) → True) → p4)))) ∨ p5)) ∨ ((p1 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226159494998815165752033509900 : (((p1 ∨ False) ∨ p1) ∨ (p1 → (((p5 ∧ ((((p3 ∧ p2) → ((p1 ∨ p1) ∨ p1)) ∨ p4) ∧ p4)) ∨ False) ∨ (p1 → (p1 ∨ (p1 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52604074965530958254895198195 : ((((False → (p4 ∧ (p5 ∧ (p4 → False)))) → ((p4 ∧ (p3 ∨ p1)) ∨ p2)) ∨ (p2 ∨ (((p3 → ((p1 → p4) → False)) ∨ p3) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_923120654979065635024678645550 : ((((((p5 ∨ ((False ∧ ((p4 ∨ p5) ∨ p4)) → False)) → p1) ∨ p1) ∧ (((p2 ∨ (p3 ∧ (p2 → p3))) → p3) ∧ ((p5 ∨ p3) ∨ p2))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h9 : (p5 ∨ ((False ∧ ((p4 ∨ p5) ∨ p4)) → False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h10 := h4 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : (p5 ∨ ((False ∧ ((p4 ∨ p5) ∨ p4)) → False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h12
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : (p5 ∨ ((False ∧ ((p4 ∨ p5) ∨ p4)) → False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h18
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855593064034074675814641929205 : ((((((((((p3 ∧ p2) ∨ p5) ∨ False) ∨ ((False ∨ ((True → (p5 ∧ (p3 ∨ (p3 ∧ False)))) ∧ p1)) → p2)) ∧ p1) ∨ p3) ∨ True) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p3 ∧ p2) ∨ p5) ∨ False) ∨ ((False ∨ ((True → (p5 ∧ (p3 ∨ (p3 ∧ False)))) ∧ p1)) → p2)) ∧ p1) ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655081129150025722940281076297 : (((((True ∨ ((((((p4 → (p4 → (((p2 → (p5 → True)) ∨ False) ∧ False))) ∧ p1) → p1) → p1) ∨ p2) ∨ True)) → False) ∨ (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626628140565579501756898758624 : ((((p4 → (p1 ∨ ((p3 ∧ (p3 → False)) ∨ ((p2 ∧ p3) ∨ ((((True ∨ True) ∨ ((p1 → p3) ∨ (p4 → p2))) ∨ p2) ∧ p4))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_115325497996828495420111675501 : ((((True → True) ∨ (False → ((True ∨ (p3 → p1)) ∧ p3))) → (True ∧ (p4 → ((p1 ∧ (p4 ∧ (p3 → p3))) → (True ∧ p1))))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639473435175884658262833055843 : ((((((False ∨ True) ∧ p5) ∧ ((((p5 ∨ p4) → p4) ∧ p2) ∧ ((p5 ∨ ((p5 → (False → p3)) → (p3 ∧ True))) ∨ (p2 ∨ p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42336681766697535456530323634 : (((p3 ∧ ((((True ∧ (((p5 ∧ ((p2 ∧ (p1 → p5)) ∨ ((True ∧ False) ∨ p1))) ∧ p5) → True)) ∨ p5) ∧ (p5 ∧ True)) → p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52787509139488666653213659773 : ((((((p3 → True) ∧ ((True ∨ p4) ∨ p1)) ∧ (p2 ∨ p1)) → (p4 → True)) → ((False ∨ ((p5 ∧ p5) → (p2 ∨ p3))) → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244415333753406960388538794080 : ((False ∧ p1) ∨ (p1 ∨ ((p2 → p4) → (((p2 ∧ (True → p2)) ∨ (p1 ∨ ((p1 ∧ (True → p4)) ∨ (True ∨ (p4 ∧ (p3 ∨ True)))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37056836875684832014492364261 : (((((((((p4 ∧ (True ∨ p1)) → True) → (p2 ∨ ((False ∧ True) ∨ p1))) → p1) ∨ (p5 ∧ ((p3 ∨ True) ∨ p5))) ∧ True) ∧ False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681243379771786340149026683360 : ((((p4 ∧ (((False ∨ p5) → True) ∨ (((p1 → (p1 → p3)) → True) ∧ ((p2 → False) → (p4 ∧ p1))))) → (p3 → (p3 ∧ (False → True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113770463133615337503961496580 : (((((p5 → (True ∧ p1)) ∨ p5) ∨ (((False ∧ ((True ∧ (p1 ∨ p1)) → ((p1 ∨ True) → p4))) ∧ p4) ∧ False)) → (p1 ∧ p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785663333173571223817683447840 : (((p4 ∨ ((((True → ((((True ∨ (p5 ∨ p5)) → p1) ∧ p1) ∧ (((False → False) → p5) ∧ p3))) → (p2 → p5)) ∧ (p1 → p4)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610630436443877461450449894633 : ((((((((((p2 ∧ (p1 ∧ ((True ∧ ((p2 ∨ p3) → p1)) ∨ p2))) ∨ p2) → p3) ∧ p5) ∨ (p4 → p4)) → (True → False)) → False) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 ∧ (p1 ∧ ((True ∧ ((p2 ∨ p3) → p1)) ∨ p2))) ∨ p2) → p3) ∧ p5) ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135043301710147329103741183421 : ((((((((p5 ∨ p3) ∨ ((False ∧ p3) ∨ p5)) ∧ ((p4 ∧ (False → p5)) ∧ p3)) ∨ p2) ∨ p1) ∨ False) ∨ (p5 → p5)) ∨ ((False → False) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60658452546188935299868363208 : ((True ∧ ((p1 → ((p2 ∨ (False ∧ (p4 ∨ p2))) ∨ (p2 ∨ (p5 ∨ ((False ∧ p2) → (False ∧ True)))))) ∨ (False ∨ ((False ∨ p2) → True)))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355870036690159655146530612593 : (p5 → (((p5 ∧ (p5 → True)) → ((p4 → (((((p1 ∧ p1) ∧ True) ∨ (p3 ∧ p1)) ∧ True) ∧ p2)) → (p1 ∨ p4))) ∨ ((p3 ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592663255094247736067556315673 : (((((p2 → (((True ∧ (p2 ∧ (p4 ∧ p2))) ∧ (p3 ∧ (True → (p5 → (((p5 ∨ p4) ∧ False) ∨ True))))) ∨ p5)) → (True ∧ p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115046371996968567870431853157 : ((((p5 → (p3 ∨ ((((p2 ∨ p3) ∧ p3) → p1) ∨ p2))) ∨ p2) ∨ (((p2 ∧ (True ∧ p1)) → (p2 ∨ (p4 → True))) → p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137631504989012493856760044255 : ((False ∨ (((p4 ∨ p3) ∧ ((p2 ∧ (((p5 ∧ p2) ∨ p2) → (False ∧ p4))) ∨ ((p1 ∨ p4) ∨ p5))) ∨ (p5 → p5))) ∨ ((p3 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138282979514064715937446855197 : ((p3 → ((p5 ∨ ((False ∨ (p2 ∨ ((((p2 ∧ p1) ∨ (True ∧ p3)) ∧ p1) ∨ (p5 ∧ p5)))) ∧ (p4 ∧ False))) ∨ p3)) ∨ ((p4 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228992094683018296049359187913 : ((p5 ∨ (False ∧ False)) ∨ ((((p2 ∨ False) ∨ ((((True ∨ p1) ∧ p2) → ((p3 → p3) ∨ (p3 ∧ p5))) ∨ False)) → (p2 → (p3 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263603704254286567786085123188 : (True ∧ (((((((p2 ∧ (p1 ∨ (p2 → p1))) → p2) ∨ p4) → (p1 → p3)) ∨ (p4 → (p3 ∨ True))) → p3) → (((p5 → p2) ∨ p2) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((((p2 ∧ (p1 ∨ (p2 → p1))) → p2) ∨ p4) → (p1 → p3)) ∨ (p4 → (p3 ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (((((p2 ∧ (p1 ∨ (p2 → p1))) → p2) ∨ p4) → (p1 → p3)) ∨ (p4 → (p3 ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254683955401034684708958926538 : ((p3 ∧ p2) → (p1 → ((((p1 ∨ (p3 ∧ False)) ∨ ((p5 → p5) ∨ p2)) → ((p2 → (p4 ∨ ((p2 ∧ p5) ∨ p1))) ∧ p1)) ∨ (p5 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112134001439918042431228669459 : (((False ∧ ((False ∧ ((True ∨ p5) → (False ∧ ((False ∧ False) ∧ p2)))) ∨ (((p2 ∧ (p4 → (p2 → p2))) → p1) ∨ p3))) ∨ True) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218143228932555955095174690120 : (((p4 → p2) ∧ (True → False)) → ((p4 ∨ ((False ∨ (p3 ∧ ((((True → p4) ∧ ((True ∨ p2) ∧ p1)) ∨ p4) ∧ True))) → p4)) ∧ (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110812201233106409709322493631 : (((((False → (p4 → ((p2 ∧ p3) → (True ∨ False)))) ∧ (p2 ∧ ((True ∨ ((p5 ∧ p4) → (p1 ∧ p4))) → p3))) ∨ True) ∧ True) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216950727125401191477974402547 : (((p1 → (p5 ∧ p4)) ∧ p4) → (p5 ∨ (p2 → (p2 → (((True ∨ (((p5 → (p5 → p4)) → p2) ∧ p4)) ∧ p3) → ((p5 ∨ p2) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h13 := h6.left
  let h14 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114231437754952100620362007239 : (((p2 ∧ (((p4 ∨ p5) → p4) ∧ ((p3 ∧ ((p1 → ((p2 → p4) ∨ p1)) ∨ True)) ∧ (True ∨ p5)))) → ((p4 → p2) ∧ p1)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60897297155266889815642799970 : ((True ∧ (p4 → (((p3 → p4) ∧ p2) ∨ (p4 → ((p4 ∨ (True → p3)) → (p2 ∨ (p5 ∧ ((False ∧ (p1 → (p4 → True))) ∧ False)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92657827187318009332808642730 : (((p1 → p1) → (((p3 ∨ (p1 ∨ p1)) ∨ (True → (((p2 ∨ ((p5 → True) ∧ (p3 ∨ p5))) → p2) ∨ p4))) ∧ (p4 ∧ (False ∧ p1)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218315982400334642314457482638 : (((True → False) ∨ (False ∨ p1)) → ((p2 ∧ (p4 ∨ (((p4 ∨ (True ∨ (False → p5))) ∧ (p5 ∨ (p2 ∧ False))) ∨ (p2 ∨ p5)))) → (p1 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h18 =>
            -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
            have h19 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h18, we can now drive its conclusion.
            let h20 := h18 h19
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- False on the left can always be used.
              apply False.elim h22
            case inr h23 =>
              -- One of the premise coincides with the conclusion.
              exact h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h30 =>
              -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
              have h31 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h30, we can now drive its conclusion.
              let h32 := h30 h31
              -- False on the left can always be used.
              apply False.elim h32
            case inr h33 =>
              -- Disjunctions on the left can always be decomposed.
              cases h33
              case inl h34 =>
                -- False on the left can always be used.
                apply False.elim h34
              case inr h35 =>
                -- One of the premise coincides with the conclusion.
                exact h35
          case inr h36 =>
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- False on the left can always be used.
            apply False.elim h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h41 =>
              -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
              have h42 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h41, we can now drive its conclusion.
              let h43 := h41 h42
              -- False on the left can always be used.
              apply False.elim h43
            case inr h44 =>
              -- Disjunctions on the left can always be decomposed.
              cases h44
              case inl h45 =>
                -- False on the left can always be used.
                apply False.elim h45
              case inr h46 =>
                -- One of the premise coincides with the conclusion.
                exact h46
          case inr h47 =>
            -- Conjunctions on the left can always be decomposed.
            let h48 := h47.left
            let h49 := h47.right
            -- False on the left can always be used.
            apply False.elim h49
    case inr h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h52 =>
          -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
          have h53 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h52, we can now drive its conclusion.
          let h54 := h52 h53
          -- False on the left can always be used.
          apply False.elim h54
        case inr h55 =>
          -- Disjunctions on the left can always be decomposed.
          cases h55
          case inl h56 =>
            -- False on the left can always be used.
            apply False.elim h56
          case inr h57 =>
            -- One of the premise coincides with the conclusion.
            exact h57
      case inr h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h59 =>
          -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
          have h60 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h59, we can now drive its conclusion.
          let h61 := h59 h60
          -- False on the left can always be used.
          apply False.elim h61
        case inr h62 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h63 =>
            -- False on the left can always be used.
            apply False.elim h63
          case inr h64 =>
            -- One of the premise coincides with the conclusion.
            exact h64
  -- Conjunctions on the left can always be decomposed.
  let h65 := h2.left
  let h66 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h66
  case inl h67 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h68 =>
      -- One of the premise coincides with the conclusion.
      exact h65
    case inr h69 =>
      -- Disjunctions on the left can always be decomposed.
      cases h69
      case inl h70 =>
        -- False on the left can always be used.
        apply False.elim h70
      case inr h71 =>
        -- One of the premise coincides with the conclusion.
        exact h65
  case inr h72 =>
    -- Disjunctions on the left can always be decomposed.
    cases h72
    case inl h73 =>
      -- Conjunctions on the left can always be decomposed.
      let h74 := h73.left
      let h75 := h73.right
      -- Disjunctions on the left can always be decomposed.
      cases h74
      case inl h76 =>
        -- Disjunctions on the left can always be decomposed.
        cases h75
        case inl h77 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h78 =>
            -- One of the premise coincides with the conclusion.
            exact h65
          case inr h79 =>
            -- Disjunctions on the left can always be decomposed.
            cases h79
            case inl h80 =>
              -- False on the left can always be used.
              apply False.elim h80
            case inr h81 =>
              -- One of the premise coincides with the conclusion.
              exact h65
        case inr h82 =>
          -- Conjunctions on the left can always be decomposed.
          let h83 := h82.left
          let h84 := h82.right
          -- False on the left can always be used.
          apply False.elim h84
      case inr h85 =>
        -- Disjunctions on the left can always be decomposed.
        cases h85
        case inl h86 =>
          -- Disjunctions on the left can always be decomposed.
          cases h75
          case inl h87 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h88 =>
              -- One of the premise coincides with the conclusion.
              exact h65
            case inr h89 =>
              -- Disjunctions on the left can always be decomposed.
              cases h89
              case inl h90 =>
                -- False on the left can always be used.
                apply False.elim h90
              case inr h91 =>
                -- One of the premise coincides with the conclusion.
                exact h65
          case inr h92 =>
            -- Conjunctions on the left can always be decomposed.
            let h93 := h92.left
            let h94 := h92.right
            -- False on the left can always be used.
            apply False.elim h94
        case inr h95 =>
          -- Disjunctions on the left can always be decomposed.
          cases h75
          case inl h96 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h97 =>
              -- One of the premise coincides with the conclusion.
              exact h65
            case inr h98 =>
              -- Disjunctions on the left can always be decomposed.
              cases h98
              case inl h99 =>
                -- False on the left can always be used.
                apply False.elim h99
              case inr h100 =>
                -- One of the premise coincides with the conclusion.
                exact h65
          case inr h101 =>
            -- Conjunctions on the left can always be decomposed.
            let h102 := h101.left
            let h103 := h101.right
            -- False on the left can always be used.
            apply False.elim h103
    case inr h104 =>
      -- Disjunctions on the left can always be decomposed.
      cases h104
      case inl h105 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h106 =>
          -- One of the premise coincides with the conclusion.
          exact h105
        case inr h107 =>
          -- Disjunctions on the left can always be decomposed.
          cases h107
          case inl h108 =>
            -- False on the left can always be used.
            apply False.elim h108
          case inr h109 =>
            -- One of the premise coincides with the conclusion.
            exact h105
      case inr h110 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h111 =>
          -- One of the premise coincides with the conclusion.
          exact h65
        case inr h112 =>
          -- Disjunctions on the left can always be decomposed.
          cases h112
          case inl h113 =>
            -- False on the left can always be used.
            apply False.elim h113
          case inr h114 =>
            -- One of the premise coincides with the conclusion.
            exact h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356520242169935796690834322078 : (p5 → (((p1 ∧ (p5 ∧ (p4 ∧ ((p5 ∨ True) ∨ p5)))) ∧ p4) ∨ ((((((p3 ∧ p4) ∧ p4) → False) ∨ p5) ∧ ((p4 ∧ p1) ∧ p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752604647176921076281791199425 : (((False ∧ ((((p1 ∧ ((p3 ∨ (p3 ∧ p1)) ∨ (p2 ∧ (((((False ∨ p5) → p4) → p1) → True) → (True ∨ p5))))) ∨ p4) ∨ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137611466898957949776682235083 : ((False ∨ ((((p4 → p5) ∧ ((((True → (True ∧ False)) → (((p5 → True) → p3) → p4)) → True) → p4)) → False) ∧ p1)) ∨ (False → (p1 ∧ False))) := by
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
theorem thm_5_vars_81022457886080395770695113471 : ((((((False → False) → p1) ∧ ((p2 ∧ p4) → (p4 ∨ (p3 → p5)))) ∧ (((p1 ∧ True) ∧ (p4 → p1)) ∨ p1)) ∧ (p2 → (False ∨ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655704471943547550061807487694 : (((((p1 ∧ ((((((p4 ∨ (False → False)) ∧ p2) ∨ (p3 ∨ p1)) → (p3 ∧ p4)) ∨ False) ∨ p5)) ∧ (p2 ∧ (p4 → p2))) ∨ (p2 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_632897003104229149265055872488 : ((((((p3 ∨ (True ∨ ((((((p3 ∧ p5) ∨ p5) ∧ p1) ∧ p5) → ((p2 ∨ p4) ∧ p3)) → p5))) ∧ (p1 ∨ p5)) ∧ (p1 → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161668626044754939412141983750 : ((p1 ∨ (p1 ∨ (((p3 → (((p2 ∨ ((p5 ∧ p3) ∨ True)) ∧ p4) → p2)) ∧ (p4 ∧ True)) → p2))) → (p5 ∨ ((p3 ∨ True) ∨ (p2 ∧ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
theorem thm_5_vars_46187192301974694912170020449 : ((((p3 ∧ ((((((p1 ∧ p5) → ((((False → False) ∨ p1) ∧ (p2 → False)) ∧ True)) → True) → p5) ∨ p4) → True)) → False) ∧ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187687916080233182911448551472 : ((False → ((((p3 ∧ False) ∨ (p4 ∧ p4)) → (p3 → True)) ∨ True)) → (p4 ∨ ((True ∨ p5) → (((p3 ∧ p1) ∨ p3) ∨ (True ∨ (p4 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109942840917547075284104040573 : ((True → ((p5 ∨ (p1 → p5)) ∨ ((p2 ∨ (((p2 ∨ (p2 ∧ p3)) ∧ (p3 ∨ p1)) ∨ p3)) ∨ (p4 → ((p2 ∨ p1) ∨ True))))) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121961389643656267401890282240 : (((False ∨ (((True ∨ True) → (False ∨ (False → (((((p3 ∨ True) → p1) ∧ p4) ∨ (False ∨ p1)) ∨ (p3 ∨ p5))))) ∨ False)) → p3) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((True ∨ True) → (False ∨ (False → (((((p3 ∨ True) → p1) ∧ p4) ∨ (False ∨ p1)) ∨ (p3 ∨ p5))))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307131502556756605516292666889 : (p1 ∨ (False ∨ (((p5 → ((((True → (True ∧ (((True → p4) ∧ (False ∨ p2)) ∨ p5))) → True) ∧ p4) ∧ (p5 → p3))) → p4) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_706754980595938531286793280832 : (((((((p5 ∨ p3) → (True → p4)) → p5) ∧ p1) ∨ (((True ∨ (p4 ∧ (False ∧ p4))) ∨ (((p1 ∨ True) ∨ p3) ∨ p1)) → (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594575553330134913574532320014 : (((((p4 ∧ (((True ∧ (False → p1)) → ((p4 → p3) ∧ (True ∧ (p5 ∧ False)))) → p4)) ∨ (((p3 ∨ p4) → p4) → (p4 ∨ True))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633509677901995169525990694528 : (((((((p1 → False) ∨ ((((True ∨ (p5 ∨ p5)) ∨ (False ∨ p5)) → False) ∧ p4)) → (((True → False) → p1) ∧ p2)) ∨ (p1 ∨ p1)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



