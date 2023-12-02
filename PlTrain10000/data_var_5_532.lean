variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57698697763443323978733059038 : ((((False ∧ p5) → p2) → ((p3 → p3) → ((p1 ∨ (p1 ∨ (p3 ∨ p4))) → ((p5 ∨ ((p2 ∨ p1) ∨ (False → (False ∧ p4)))) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631364452390193241496288654877 : (((((((((((True → p4) ∨ (p3 → p2)) → p2) ∧ p3) → (p1 ∧ p4)) ∧ (p5 → (True ∧ (p2 ∧ True)))) ∧ (p5 ∨ p3)) → p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719863007516191053185675961901 : ((((p3 → (p1 → (p5 ∨ p5))) ∨ (False ∨ (p5 ∨ (p2 ∨ ((p3 ∧ (((p5 → (True ∨ p2)) → (p3 → p3)) → True)) ∨ (False → p3)))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_178807859021787458044066449489 : ((((p2 → p5) → False) ∨ ((p4 ∧ (((p4 ∨ p3) ∧ p1) ∨ p2)) ∨ p3)) ∨ ((False → ((p2 → p5) ∨ (p1 → p4))) ∨ (p4 → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356740186597047545878644877478 : (p5 → ((p4 ∧ ((p5 ∨ (True ∨ p5)) → False)) ∨ ((p1 ∨ ((p2 → ((True → p2) → (p1 → (p1 ∨ p3)))) ∨ True)) ∧ (p1 → (p1 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588930481633239119624372677835 : (((((p4 ∨ (p2 ∧ ((((p1 → p3) → (p1 ∧ (False ∧ (p1 ∧ (p4 ∧ True))))) ∧ (p5 ∧ (p4 → (p1 ∧ p5)))) ∨ p2))) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114339752534426063840215362769 : (((False ∨ ((True → ((p5 → (False → (p3 ∨ p1))) ∧ p3)) → (((p4 ∨ p4) → p2) → p5))) ∧ (p3 ∨ (p5 ∧ (p2 ∧ p1)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715234493040607896593375499963 : ((((p1 → ((p2 → True) ∧ (p1 ∨ True))) → (p2 ∧ (False ∧ (((p5 ∧ (p3 ∨ p2)) ∨ p1) ∧ (True ∨ (p5 ∨ (p5 ∨ (p3 ∧ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119151696864675477281878189582 : ((p2 → (((p5 ∨ (((((False ∨ (p3 → (p3 ∨ p2))) ∨ p3) ∧ (p2 ∧ p4)) ∨ (p3 ∨ (False → p2))) → p3)) ∧ p3) ∧ p2)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190452762592769741380851025504 : (((p3 → (p4 → ((p1 → (p1 ∧ p5)) → p2))) ∨ False) ∨ ((p4 ∨ False) → ((p4 → (((p3 → p5) ∧ (p1 ∨ p4)) → p3)) ∨ (p4 ∨ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38644538357839447601193276821 : (((((((p3 → (p4 → p2)) → p2) → p2) ∨ p3) → ((((True → (True ∧ False)) ∧ p2) → (p4 ∧ ((False ∧ p3) → p3))) ∨ p4)) ∧ True) ∨ p1) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50346027297628864098534416452 : (((((p4 → p5) ∨ (p5 ∨ (p2 ∨ p4))) → (((True → p4) ∧ ((p2 ∨ True) ∧ p2)) ∨ (p2 ∨ p3))) ∨ (True ∧ ((False → p2) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702880791652795670242336900864 : ((((((p3 ∧ (p1 ∨ p1)) → p1) → ((p5 ∧ p1) ∨ p1)) ∨ (p4 ∨ ((p2 ∨ (p2 → True)) ∧ ((False → (p4 → (True → p1))) ∨ p3)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105912182447374590536089200630 : (((((p1 ∧ (((p1 ∨ (p4 ∧ True)) ∧ True) ∧ p2)) → (p3 ∧ p4)) ∧ p2) ∨ (p1 → ((p5 ∧ (p5 ∧ p2)) ∨ (p1 ∧ True)))) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59503902622680571301479719948 : (((p2 → False) ∨ (((((False ∨ ((p3 ∨ False) ∧ p5)) ∨ ((False → False) ∧ (p1 → p3))) → p2) ∧ False) ∨ (False → (True → (p3 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310801003573552352478001720304 : (p2 ∨ ((p1 ∧ (p4 → p3)) ∨ (p5 → ((((p3 ∧ ((p5 ∧ p5) ∨ ((p5 → p2) → False))) ∨ ((p3 ∨ p1) ∨ p4)) ∧ False) ∨ (p5 ∨ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37899456616630195821489708852 : (((((((p5 ∨ p2) ∨ (((p2 → True) → p1) → p5)) ∧ (p1 ∨ (p1 ∧ ((p3 ∨ p4) ∧ p2)))) → (p4 → p3)) ∧ (p2 → True)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64687152948006976650131686517 : ((p1 ∨ (p5 ∨ (((((p3 ∨ (True → p3)) ∧ (p5 → (False ∨ ((p2 → p4) ∨ p4)))) ∨ (((p1 ∨ p3) → True) → p5)) ∧ p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190914367301241099319879967143 : (((p5 → (False → (p3 ∨ (True ∧ False)))) → (p3 ∨ p1)) ∨ (((p4 ∨ p3) → (p4 ∧ (((p4 ∨ p2) → ((False → p3) ∧ p1)) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135610915965025538273293642862 : (((p3 ∧ (((p1 ∨ ((True ∧ (p1 ∧ p3)) ∧ p1)) ∨ (p3 ∨ p4)) ∧ (p4 ∧ p3))) ∨ (p5 → (p1 ∨ (p5 ∨ p1)))) ∨ ((True ∧ True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111193862457227146039773277704 : (((((False → False) → True) ∧ (((p1 ∨ (p5 → ((p5 → False) ∨ (False → (p2 ∧ p1))))) → (True → (p1 ∧ p4))) ∨ p1)) ∧ False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115862548564497856338938292257 : (((p2 → ((p1 ∧ p1) ∧ p3)) ∧ (((p1 ∧ (False ∧ (((p2 → p1) ∧ p2) ∨ p5))) ∧ ((False ∨ p2) ∧ (p4 → p5))) ∨ True)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50344380629298566620721104364 : (((((p3 → ((p1 ∨ p2) ∧ False)) ∧ p4) → ((p4 ∧ (False → (p1 ∨ (p5 → p5)))) → (p3 → p1))) ∨ (False → (p4 ∨ (False ∨ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315108986367835022170395874631 : (p3 ∨ (((p3 ∨ (p4 ∨ (p5 ∨ True))) ∧ p2) ∨ (True ∨ (((p2 ∨ p4) ∨ (p3 ∧ ((False ∨ True) → ((p1 → p2) ∧ p1)))) ∧ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135790398879665728567332336793 : ((((True → ((False → True) → p2)) ∨ (p3 ∧ (p4 → (p3 ∨ (False ∨ p2))))) → ((p5 → (p1 → (p4 ∧ p1))) ∨ p5)) ∨ (p1 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686412774657564362186142726411 : (((((p3 → (True ∨ (True → False))) ∨ (((True → p1) ∧ (p4 ∧ p3)) ∧ (True → (p4 → True)))) → (False ∧ ((p4 ∧ p2) ∧ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793253707039740131068735470941 : (((True → (p2 ∧ (((p4 ∨ p3) ∨ ((p4 ∨ ((p3 → ((True ∧ p1) ∧ (p1 ∧ p3))) ∧ p2)) ∧ (((p5 → p2) → p5) → False))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222125692664061916071684302827 : (((p3 ∨ p4) → True) ∧ (((((((p3 ∧ p4) ∧ True) ∧ p5) ∨ p2) ∨ (p3 → (p1 ∨ (p5 → p5)))) ∨ False) ∨ (((p3 → True) ∨ True) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_669580970789128313567356830188 : ((((((p3 ∧ (p2 ∧ p4)) ∧ (((p2 ∧ (((True ∧ p4) ∨ p3) ∧ p3)) ∧ p2) → p4)) ∧ ((p5 ∧ p3) → p4)) ∨ ((p1 ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54030254406273516651957433575 : ((((((p5 ∧ p2) ∨ (p4 ∧ p2)) → p3) ∨ (p2 → p2)) → (True → (((((p1 ∨ p1) ∧ (p3 ∧ p2)) ∧ (p2 ∧ p4)) ∨ p3) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192383909698421729020181742627 : (((((p1 → (p3 ∨ (True → p5))) → p3) ∧ p4) ∨ p5) → ((((p1 ∧ (True ∨ (p1 → (False ∨ p1)))) ∧ p3) → (p5 ∨ (p1 ∧ False))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117944404181472569762565805994 : ((p5 ∧ (p3 ∧ (p5 ∧ ((((p4 ∧ (p4 → (((p3 ∨ p4) ∧ (True ∧ p4)) ∧ ((True ∧ True) ∨ p4)))) ∧ p2) ∨ False) ∧ True)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320457361682451308792483217709 : (p4 ∨ ((True → False) → ((((((p5 ∨ (p3 ∨ False)) ∨ (p4 ∧ ((False ∧ p3) ∨ (((p1 → p1) → p3) ∨ p5)))) ∨ p4) ∨ p4) ∧ p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756779101837262784163532631591 : (((p1 ∧ ((p5 ∧ ((((p4 ∨ p1) → (p3 ∧ p4)) → p3) → p3)) ∧ ((True ∨ (p4 ∧ (((p2 ∧ p1) ∨ p5) ∨ p1))) → (p2 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111694213680474594913020256829 : (((((((False ∨ (p5 ∧ ((p1 → (p5 → p2)) ∧ (p3 → (p2 ∧ p2))))) ∨ True) → (p1 ∨ (p5 ∨ p3))) → True) → p1) ∨ True) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347136499321097493173018380290 : (p3 → (((((p2 → (p3 ∨ (p5 → p4))) → p3) ∧ p3) ∨ ((p5 → p3) → True)) → (p2 ∨ (((True ∧ ((p4 ∧ p5) ∨ False)) ∧ p1) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150079297729158321997656913026 : ((True → (True ∧ ((p4 → (p5 → p1)) → ((p4 ∨ ((p4 → (p5 ∧ (False ∧ (p5 ∧ p2)))) ∧ p5)) ∧ p2)))) ∨ (p3 → (True ∨ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147379221531744612146867605381 : ((((p4 ∨ ((True → ((p3 ∧ p5) ∧ p4)) ∨ (p2 ∨ p3))) ∧ (((False → p4) → p5) ∨ (p5 ∧ False))) ∨ True) ∨ (p3 ∧ (False → (p2 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783014737472307228741681876642 : (((p3 ∨ (((p2 ∨ False) → (p5 ∨ (((p3 ∧ p1) ∧ (((p4 ∨ p3) ∨ (True → ((p3 → p1) ∨ p1))) ∨ p3)) ∨ p3))) ∨ (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177863813269330068473688487005 : (((((p2 → p1) ∨ ((p2 → ((p4 ∨ p1) ∧ False)) ∧ p3)) ∨ p5) ∨ p5) ∨ ((((((p5 ∨ True) ∧ p5) ∧ p2) ∧ p3) → (p2 ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199325489892449786029517340150 : ((((((False → p5) → p1) ∧ p3) → True) ∨ p5) → ((p2 ∨ (((p1 ∨ (p3 ∨ p2)) ∧ p2) → (p1 ∨ True))) ∧ (True → ((p4 → p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
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
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608413671923931033940498971889 : (((((((((p3 ∧ (True ∧ p5)) ∧ p1) → ((((p5 ∨ False) ∧ (((True ∧ p1) ∧ p1) ∨ False)) → p5) ∨ True)) ∧ True) → p1) ∨ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681413396340561856555122840959 : ((((p3 ∨ ((((True ∧ p2) → p2) ∨ (p1 → (p4 → ((False ∧ (p5 ∨ p5)) → (p3 → p1))))) ∧ p5)) → ((p3 → (True ∧ p3)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118650705976573309093481377269 : ((p4 ∨ (p2 ∧ ((p3 → (((((p4 ∧ p5) → (p1 ∨ (False ∧ (p4 ∨ False)))) ∨ p5) → False) ∧ False)) ∨ (p3 ∧ (p5 ∨ True))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54825291220808306388852709453 : (((False → (((p5 ∧ True) ∧ p3) ∨ (p5 ∧ p1))) → (p5 ∨ ((p5 → (p1 ∧ ((False → ((p5 → False) ∧ True)) ∧ (True ∧ p5)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57779018517824589980228679585 : (((True ∧ (p4 → p3)) → (((p4 ∧ (((p3 ∨ (p2 ∧ p4)) ∨ p2) ∧ (((p5 → p5) ∧ (True ∧ True)) ∧ (False ∨ p5)))) ∨ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150761627875756589692771445848 : ((((p5 → (((((p1 → p4) ∨ p5) ∧ ((p3 ∧ p2) → True)) ∨ (p1 ∧ p2)) ∨ (True → p1))) ∨ p4) ∨ True) → ((p1 → p3) ∨ (True ∨ p4))) := by
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
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47337885579712345733282272987 : ((((False ∨ True) ∧ ((p1 ∨ (((p4 ∧ (p1 ∧ False)) ∧ True) → (p4 → (((True ∨ True) ∧ p1) ∨ False)))) → (p1 ∨ p5))) ∨ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199214113748308696672820626567 : (((p2 ∨ ((p5 → (p2 ∨ True)) → p5)) ∧ p3) → ((p5 → (p3 → (((False ∧ True) ∨ ((True → p1) → False)) ∨ (p3 ∨ (False ∨ p3))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41519019101268412937013567010 : (((((((p1 ∧ p2) → False) ∧ p1) ∨ ((True → p5) ∨ p1)) ∧ ((((p5 ∧ (p3 ∧ (p3 ∧ p3))) ∧ (p5 → p5)) ∧ True) ∨ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41987715096175647057857907778 : ((((p5 ∨ False) ∧ ((p1 → ((False → (True ∨ True)) ∧ (False ∧ (True → ((True → p2) ∨ ((p3 → (p5 ∧ p3)) ∧ p2)))))) ∧ p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725728673864491111003126000980 : (((((p1 ∨ p2) ∧ p2) ∨ (((p2 ∧ p3) ∧ p1) → (p3 → (False ∨ (False ∧ ((((False ∨ (p5 ∨ (False ∧ p3))) ∨ p5) ∨ p5) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165031812945272378458678821526 : (((((p3 → p3) ∧ False) → ((p3 → ((((True ∨ p5) ∨ p1) → p2) ∨ p1)) ∨ p1)) → p5) ∨ (((p3 ∨ (p1 ∧ p5)) → p4) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134132967866171784818090601018 : (((((((p4 ∨ p1) ∨ (p3 → ((((p4 → False) → p2) ∧ False) ∧ p2))) ∨ p1) → (p1 ∨ True)) → (p5 ∨ False)) ∨ p5) ∨ ((False ∧ p2) → p3)) := by
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
theorem thm_5_vars_113453704396267633211651935540 : ((((((p4 ∧ (p4 ∨ (p3 → ((p2 → (p4 ∧ p3)) ∧ False)))) ∨ ((p4 ∧ p5) → (False ∧ p4))) ∨ False) → p1) ∨ (p5 ∧ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39888660178323218535274835365 : (((p2 → ((p5 ∧ (False → p4)) ∨ (((p1 → (p1 ∨ ((p1 → (False ∧ (p2 ∧ False))) → (True ∧ (p2 ∨ p5))))) → p4) ∨ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213617349155771359570059912901 : ((((p1 ∧ p3) ∨ p1) ∨ p5) ∨ ((p5 ∧ (((False ∧ p4) ∨ p3) ∨ True)) → ((((False → (p2 ∧ (True ∧ p4))) ∨ p3) → False) → (p2 → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : ((False → (p2 ∧ (True ∧ p4))) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309680430217398386662104678768 : (p2 ∨ ((((p4 ∨ False) ∧ (p5 ∧ (((p5 ∧ ((False ∨ (p2 ∧ True)) → True)) ∨ p2) → (False ∨ (True ∧ p2))))) → p5) → ((p5 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612724832703059763133659815596 : ((((((True ∨ (((p3 ∨ p3) → False) ∨ (p1 → p2))) → (p4 ∨ (p3 ∧ (False ∨ (p3 ∨ (p3 ∧ (True ∧ False))))))) ∨ (False → p5)) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_250704855708139704244329537238 : ((p1 → False) ∨ (((p3 ∧ p4) ∧ (p5 → ((False → p1) → (p4 ∨ (((False → True) → p4) → (False ∧ False)))))) ∨ (((p2 → p2) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238192054104374590450174207312 : ((True ∨ p4) ∧ ((((True → ((p1 ∨ p5) → (False ∨ (p1 → ((p3 → False) → p4))))) ∨ p2) ∧ (p5 → (p4 ∨ True))) ∨ ((False ∧ p1) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675271450979770918254763568 : ((((p5 → ((p4 ∨ (p1 ∧ False)) ∧ p3)) ∨ (((p2 ∨ (p2 ∧ p5)) → p2) → p1)) ∨ (((True ∧ (p3 → True)) ∨ p3) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351574906375169782364359515717 : (p4 → (((p4 ∧ (True ∨ True)) ∨ ((((p5 ∧ (p2 ∧ False)) ∨ p3) ∨ ((p5 ∨ p1) → p5)) ∨ p4)) → ((p1 → (False ∨ p5)) ∨ (False → p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
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
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122150655156428355465787520419 : (((((p5 → ((p2 ∨ p5) ∨ (False ∨ ((False → p2) → ((True ∨ (p2 ∧ True)) → (p5 → p2)))))) ∨ p4) → p5) ∧ (p4 → p4)) → (True ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → ((p2 ∨ p5) ∨ (False ∨ ((False → p2) → ((True ∨ (p2 ∧ True)) → (p5 → p2)))))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657048074932978224834779972027 : ((((((False → True) → p5) ∧ (p1 ∧ (p3 ∨ (p5 ∧ ((False ∧ p3) ∨ ((p1 ∧ p5) ∨ ((p4 ∨ True) ∧ (True ∨ p5)))))))) ∨ (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45161121455082058711435228393 : (((True ∧ (((p5 ∨ p1) ∨ ((p1 ∨ (((p4 → ((p4 → p1) → p5)) ∨ p5) ∧ (p1 ∨ False))) ∧ p4)) ∧ ((p5 ∨ p5) → False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112872580617647267083513355080 : ((((True ∧ (False ∧ p4)) → ((p5 ∧ (((((True ∨ p5) ∧ False) ∧ (p2 ∨ p5)) ∨ p5) → (p3 ∨ (p3 ∧ p1)))) ∨ True)) → False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83833894184623650781831349147 : (((((p3 → True) ∧ ((p3 ∧ (p3 ∨ False)) → False)) ∨ (True → ((p5 ∨ (p2 ∨ p4)) → True))) → (p1 ∧ (((p2 ∨ p3) → p3) ∧ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → True) ∧ ((p3 ∧ (p3 ∨ False)) → False)) ∨ (True → ((p5 ∨ (p2 ∨ p4)) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2076236575740873226924232442 : ((((p3 → ((p5 ∧ p1) → p4)) ∨ (p4 ∧ (((False → (False ∧ False)) ∧ p1) ∨ p1))) → p3) ∨ (p4 → ((p1 → (p3 ∨ False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777696077888933369851444526774 : (((p1 ∨ ((False ∨ ((((p3 ∨ p1) ∧ p2) ∧ False) ∨ p4)) ∨ (((False ∧ (p5 → p2)) ∨ ((p3 ∨ ((p4 ∧ p1) ∨ False)) → p1)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54682236027211920092471312758 : (((((False → False) ∧ ((p2 ∨ p3) → p4)) → p5) → ((p3 ∨ p3) ∧ ((p1 ∨ (True ∧ ((True ∧ p1) ∨ ((p3 ∧ p1) ∨ p4)))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702066312367555990531188509977 : ((((p1 → (((False → (p4 → p5)) → p4) ∧ (True ∨ p2))) ∧ ((p3 ∧ ((((p5 ∨ p4) ∨ True) → ((False ∨ p3) ∨ p2)) ∨ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68704603914207132889387696711 : ((p4 → (((False ∨ p5) ∨ ((p1 ∧ ((((p5 ∧ False) → p5) → (p4 ∧ (True → p5))) ∨ (False ∧ (p3 → True)))) → p4)) → (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307180527930751881323126962368 : (p1 ∨ (p1 ∨ (((p3 → (p1 → ((False ∨ p3) ∧ (False ∨ (p1 → (p2 → ((True → ((p1 ∨ (True → p3)) ∨ True)) ∨ p3))))))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51123805664659241726512003338 : (((((p5 ∧ ((p5 ∧ p4) → p2)) → (((p1 ∧ (p1 → p4)) ∧ p2) ∨ (p2 ∧ p5))) ∨ p4) ∨ (True ∨ (((p3 ∨ False) ∨ False) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303458400057780831419421602478 : (p1 ∨ (((((((((p4 → (False → False)) → p2) ∨ p5) → p1) ∧ p5) → ((True → False) → p4)) ∨ True) → ((p2 ∨ True) ∨ (p2 ∨ False))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7808554610117641419802362516 : ((((((p2 ∨ ((p4 ∧ False) ∨ True)) ∨ p4) ∧ ((True → ((True ∧ (p1 ∧ (p5 ∨ (p3 ∨ False)))) ∧ (p1 ∨ p4))) ∨ True)) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614205973939296636438184443898 : (((((((p2 ∧ (p5 ∧ (p4 ∧ p4))) ∧ ((p1 → (p1 → p2)) ∨ (p5 ∨ ((False → p4) ∧ False)))) → p2) → ((p2 ∨ p3) ∧ p5)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113903505135666073884777235795 : (((((p5 ∧ False) → (((p4 ∨ (False ∧ ((p2 ∧ (p3 ∨ (True ∨ p1))) → p3))) ∨ p4) ∨ p3)) → p2) ∧ ((p5 → p3) ∧ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133398323517884992373509710434 : ((p4 → (((p2 ∨ ((((False ∧ (False ∨ p3)) ∨ False) ∨ (False ∧ p3)) ∧ (p3 ∨ (p1 → False)))) ∧ p4) ∨ (p5 → True))) ∧ (p5 → (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208965440369506978009995847420 : ((True ∨ ((p4 ∨ False) ∨ (p2 ∧ True))) → (((p3 → (False ∨ (p5 ∨ p3))) ∨ ((p3 ∧ p2) ∧ ((p5 ∧ p2) ∨ p2))) ∨ ((p3 → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688999451052949270241295862091 : (((((((p3 ∧ (((False ∧ (p5 ∧ False)) ∨ p1) → (p3 ∧ True))) → True) → p5) ∨ p2) ∨ (((p4 ∧ p2) → (p2 ∨ (p3 ∨ p3))) ∨ p5)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1604451249972284818797924999 : (((p1 ∨ (p3 ∨ ((((((p3 ∨ (p1 → p3)) ∨ True) ∨ (p4 ∨ p4)) ∧ True) ∨ p3) ∨ ((True ∨ p3) ∧ p4)))) → p4) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p3 ∨ ((((((p3 ∨ (p1 → p3)) ∨ True) ∨ (p4 ∨ p4)) ∧ True) ∨ p3) ∨ ((True ∨ p3) ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323778506885846199448721916617 : (p5 ∨ (((((p4 → p4) → (p2 ∨ (True → True))) ∧ (p5 → ((p3 ∧ (False ∨ p4)) ∨ p4))) ∧ True) ∨ ((((p3 ∨ True) ∧ p3) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164578521959161983286774899623 : (((((p3 ∨ False) → p2) → (p3 ∨ (((p1 ∨ False) → p2) ∨ (False ∧ (False ∨ p5))))) ∧ False) ∨ ((p2 ∨ (False ∨ (p5 ∧ (p2 ∧ p3)))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306548357971251855774985163375 : (p1 ∨ ((True ∨ True) → (((p1 ∨ (((((False ∨ p5) ∨ True) ∨ p4) ∧ p5) ∧ ((p5 ∧ (p5 ∨ p4)) ∨ p1))) → p1) ∨ ((p5 → p4) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113145391278672829853651471415 : (((p3 → (((p2 → p1) → (((((((p2 ∨ (p2 ∨ p4)) → (False ∨ False)) ∨ p5) → p5) ∧ p2) ∧ p4) → p3)) → p5)) → p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258810839715576964521644226564 : ((True → False) → (p4 ∨ (True → ((p4 ∨ p2) → (p3 ∨ (p1 ∧ ((p3 → (p5 → p4)) ∨ (((p4 ∨ p3) ∧ False) → (True ∨ (p4 ∧ p2)))))))))) := by
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
theorem thm_5_vars_233558455113203639813470272392 : ((p1 ∨ (False → False)) → (((p4 ∧ p4) ∨ p5) ∨ ((((p4 ∧ False) ∨ ((p3 → p2) ∨ True)) ∨ (p4 ∧ ((False ∨ p3) → (p2 ∨ p2)))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63973120739797877165702731447 : ((False ∨ (((((p2 → (((True ∧ ((p1 → p4) ∧ p5)) ∨ False) → p4)) ∨ p2) ∨ (((p4 ∧ p3) → p1) ∨ True)) → (p2 ∧ p3)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310305313255565078106474389676 : (p2 ∨ (((p2 ∨ p2) ∧ ((p2 → (p3 ∧ (p4 → True))) → p1)) ∨ ((p1 ∨ ((p3 ∨ (p5 ∧ (p2 → True))) ∨ p4)) ∨ ((False ∨ True) ∧ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324292812083273275913246875640 : (p5 ∨ (((((p3 ∨ p4) → p5) → p2) ∧ (p4 ∨ False)) → (((p5 ∧ (True ∧ p1)) → False) ∨ (((p1 ∧ (p3 ∨ True)) ∧ (p4 → p3)) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184497525778783001017027639989 : (((((p1 ∧ p5) ∨ False) ∨ ((p2 ∨ p1) ∧ False)) ∨ (p2 ∨ False)) ∨ ((p5 ∧ False) → (p1 ∧ ((p3 ∨ ((p3 ∨ True) → p5)) ∧ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248186407561111045308145078332 : ((p2 ∨ False) ∨ (p1 → (p4 → (((p5 ∨ (((((False ∧ p2) ∨ p2) → p5) ∨ p4) ∨ p1)) → ((p5 ∧ (p2 ∨ p5)) ∨ p2)) ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319042801875576893964464277306 : (p4 ∨ (((p4 ∧ ((((p1 ∧ p4) → ((p5 ∧ True) ∧ True)) ∨ p4) ∨ p5)) ∧ (False ∧ (p1 → (p3 ∨ True)))) ∨ (p3 ∨ (p1 → (p5 → True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140626932735815091202224748078 : (((True ∨ ((p3 ∧ ((True ∧ (((p1 ∧ p3) ∧ p1) ∨ True)) ∨ p2)) → (p4 ∨ p5))) → ((p1 ∨ (True ∧ True)) ∧ False)) → (p4 ∨ (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p3 ∧ ((True ∧ (((p1 ∧ p3) ∧ p1) ∨ True)) ∨ p2)) → (p4 ∨ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173207221946512934923532546405 : ((p5 ∨ (((p4 ∨ p4) ∧ ((p2 → p2) ∧ (p2 ∨ p2))) ∨ ((p2 ∨ p3) ∨ p2))) ∨ (p5 → (True ∨ ((p1 ∧ p2) → ((p4 ∨ p4) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358179383021734669554671000550 : (p5 → (p3 ∨ (((p4 ∧ False) ∨ ((True → ((p3 → p1) ∧ False)) → p2)) ∨ ((p5 ∨ p1) ∧ (p5 ∨ (p5 → (p4 → ((True ∨ p1) ∨ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351336833394335972998929567196 : (p4 → ((p5 → ((p2 ∧ ((False → (p4 → ((p5 ∧ (((True → p5) → False) → p1)) ∨ (False ∨ p5)))) → p2)) → p5)) → ((p1 ∧ p4) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113964407763487903546472972403 : (((True ∧ (((True → (p3 → p1)) ∨ p3) ∨ ((True ∧ (p3 → (p2 ∧ False))) ∧ ((p1 → p2) → p2)))) ∧ ((p3 ∨ False) ∧ p4)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



