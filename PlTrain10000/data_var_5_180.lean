variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326979841923889227803743588757 : (True → ((((p1 ∧ ((p1 ∨ (p4 ∧ p4)) ∨ (p2 ∧ False))) ∧ ((False ∧ ((p1 → p4) ∨ (p1 ∨ p5))) → p4)) ∨ (True → (True ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316596345393321152504441719021 : (p3 ∨ (p3 ∨ (True → ((p1 ∧ (p2 ∧ (p3 → ((p3 ∨ False) → ((p1 ∨ (p1 → (p4 ∧ p2))) ∨ p1))))) ∨ (((p3 → True) ∨ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70095283091809240638183242634 : (((((((p4 ∨ (p5 ∧ (p1 → (p2 → True)))) ∨ p4) ∨ p4) ∨ (((((p1 → p2) → p4) → False) ∨ (p4 ∨ p3)) ∨ True)) → False) ∧ True) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 ∨ (p5 ∧ (p1 → (p2 → True)))) ∨ p4) ∨ p4) ∨ (((((p1 → p2) → p4) → False) ∨ (p4 ∨ p3)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346340250295105670113187144211 : (p3 → (((p1 → ((((True → p3) ∧ p5) → p4) ∧ (False → p3))) → ((p2 ∧ (p1 ∧ p2)) → (((False ∨ False) ∨ p4) → False))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219941129172045910127296404037 : ((p4 → (p3 → (p4 ∨ False))) → ((True → ((p5 ∧ (p5 ∧ p5)) → (((True → True) ∨ p5) → False))) ∨ (p5 ∨ ((p1 → (p3 → p1)) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225216605454434800376811761107 : (((p5 ∧ False) ∧ p4) ∨ ((p1 ∨ (p3 → (((p2 ∨ (p3 ∨ ((p3 ∨ True) → (p4 ∨ p1)))) ∨ p1) ∨ (p1 ∧ ((p1 ∧ p2) ∧ p2))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_138002681311178160306388436031 : ((p5 ∨ (p1 → ((((p5 ∨ (p3 ∧ p5)) → p4) → p2) ∨ ((p5 ∧ (p5 ∨ (True → p2))) ∨ ((False ∨ p4) → False))))) ∨ (p4 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258766534353346211253489196935 : ((True → False) → ((p2 ∧ (((p2 ∧ p1) → (p3 ∧ ((True → (False → (p2 ∧ p5))) ∧ True))) ∧ (((p3 → (p2 ∧ p1)) ∨ True) ∧ p3))) ∨ p4)) := by
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
theorem thm_5_vars_322274264913591126509157381938 : (p5 ∨ (((p4 → (((((p2 ∨ p1) → p1) → ((False → p4) ∧ False)) → (p5 ∨ p5)) ∨ (True ∨ (False ∧ ((p3 → p3) → p5))))) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41557604916508020029005201136 : (((((p1 ∧ (p5 → (p4 ∧ ((p5 → p5) → p4)))) → True) → (((p4 ∧ True) → p2) → (p2 ∨ (((p1 ∧ True) ∧ False) → p1)))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679797834788940583040008319237 : ((((((p3 ∨ p4) ∨ ((p1 → p3) ∨ ((True → (((True ∧ True) ∧ (False ∨ p1)) ∨ False)) → p5))) ∨ True) → (p5 ∧ (p5 ∧ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159303238688007144250205290645 : ((p5 → (((p3 ∧ (p1 ∧ (False ∧ p2))) ∨ (p1 → ((False ∨ ((p2 ∨ p3) ∨ True)) ∧ p1))) ∧ p1)) ∨ (False → (p1 → ((p3 ∧ p2) → p4)))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693824040035528380338886823199 : (((((((p4 → p5) → (p1 ∧ p4)) ∧ ((p2 ∧ p1) → (p2 → p4))) → p3) ∨ (False → (((True ∧ ((p1 → False) ∧ p5)) ∨ p1) ∨ True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_148343841361818586959816652244 : ((((p4 → (p2 ∨ (False ∨ (p1 ∧ p4)))) ∨ ((p4 ∨ p5) ∧ (p4 ∨ False))) ∧ (p5 → ((p1 ∧ False) → p2))) ∨ ((False → p3) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172715211780663047682408530533 : (((p4 ∨ False) ∨ (p2 ∧ (((p5 → True) → (p5 ∧ ((p5 → p1) ∧ False))) ∧ p3))) ∨ (False → (False → (p3 → (p2 → (p4 → (False ∨ False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760244038652465106143211396806 : (((p2 ∧ ((p5 → p3) ∧ ((p2 ∧ ((p3 → p3) ∧ (False ∧ ((p4 → (p3 ∨ (((p1 ∧ (False ∨ p5)) ∧ p3) ∧ p1))) ∧ p2)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340904610612160452701037211147 : (p2 → (((((p4 → p1) ∨ (p3 ∨ ((p1 ∨ p2) ∧ p3))) ∨ p1) ∨ (p3 ∨ ((False ∧ ((False ∨ p5) → p2)) ∨ (False ∨ (False → p4))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606534045153156912721302063208 : ((((((((True ∨ p2) ∧ (p5 ∨ ((p1 ∧ ((p2 → p1) ∧ (True ∧ p1))) → (p5 ∨ (p4 ∨ p3))))) ∨ (False → p5)) → p3) ∧ False) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_50893241352381640610668441535 : ((((p5 ∧ (((((True ∧ p2) ∨ False) ∧ ((p3 ∨ (p4 ∨ False)) ∨ p2)) ∨ p1) ∧ True)) → p3) ∧ ((((p1 ∨ p1) ∧ p1) ∨ p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150069930344397776131306629478 : ((True → ((p2 ∧ ((p1 ∨ (False ∧ p3)) ∧ p4)) ∧ (p4 → ((((p3 ∧ p4) ∨ p5) → p3) ∧ (p5 ∨ p3))))) ∨ (((p1 ∨ False) ∧ True) → p1)) := by
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
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82185160569954676355759137442 : (((p3 → (((p5 ∧ (p5 ∧ ((p1 ∧ (p1 → (p5 ∧ False))) ∧ p5))) ∧ (False ∨ ((False ∨ False) ∧ True))) ∨ True)) → (False ∧ (True → p5))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (((p5 ∧ (p5 ∧ ((p1 ∧ (p1 → (p5 ∧ False))) ∧ p5))) ∧ (False ∨ ((False ∨ False) ∧ True))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233908466568631448151032349833 : ((p4 ∨ (True → p2)) → ((p3 ∨ (p5 ∧ (p5 → ((((p4 → p5) → ((p3 ∧ p3) ∧ False)) ∨ (True ∧ (p2 ∨ p5))) ∨ p1)))) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_330843750895283016804327513445 : (True → (p3 → (((((p3 ∧ (p5 ∨ (False → p5))) ∨ p4) → p5) → (((True ∨ p5) ∨ False) ∧ (p2 → ((p2 ∧ p4) ∧ (p5 → False))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118495739804452820612314144962 : ((p3 ∨ ((p3 ∧ (((False → p4) → p4) → ((True ∧ False) ∨ (True → (p3 ∧ p5))))) ∨ (p3 ∨ ((p1 → p4) ∧ (p1 ∧ False))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170552426914917241603237305995 : (((p4 ∧ p1) ∨ (p4 ∨ ((p5 ∨ True) ∨ (p4 ∨ ((p3 ∧ (p1 → True)) → p5))))) ∧ (((p4 ∧ (False → (p4 ∧ p4))) ∨ (True ∨ True)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112112271389211760319760163046 : ((((False → p5) → (((((True ∨ (p4 ∨ (True ∧ p1))) → True) ∨ (p2 ∧ ((p1 → (True → False)) ∨ p3))) ∧ False) ∨ False)) ∨ p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322392785635241354175504197997 : (p5 ∨ (((p3 ∧ (((p3 → ((p2 → p2) → True)) ∧ p4) ∨ (p1 ∨ (p5 ∧ False)))) ∧ ((p4 → p4) ∧ (((p2 → False) ∧ True) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698091032950904995077244171785 : (((((p3 ∧ (True → ((p3 ∧ ((p5 ∧ p2) ∨ p4)) ∨ p1))) ∨ False) ∨ ((p3 ∧ (((p1 ∧ (p1 → p3)) ∨ p5) ∨ (p3 ∧ p2))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49818724158400548343971839672 : (((p2 → ((((p2 ∨ (((p2 ∨ (False → p5)) → p3) ∨ True)) ∨ ((p5 ∧ p1) → p2)) ∨ p4) ∨ (False → p3))) → (p5 ∨ (p3 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193330535033733931426868788853 : ((((True ∨ p3) ∧ p2) → (((p5 → p3) ∧ p1) → p4)) → (p3 → ((p3 ∧ ((((p5 ∨ False) ∨ False) ∧ p1) ∧ (p4 → (p2 ∧ True)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173821387896511765298209305411 : (((p1 ∨ (p1 → ((((p2 → ((False ∧ p3) → p1)) ∧ False) ∨ True) ∧ False))) ∨ p1) → (((p3 ∧ p1) → (p2 ∨ ((p3 ∨ False) ∧ p4))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_214784756154743627031145242167 : (((False ∨ p4) ∨ (p4 ∨ p2)) ∨ (p5 → ((((p4 ∧ p5) → (False ∨ p4)) ∨ (((((False → p2) ∨ (p5 ∨ p5)) ∨ p4) → p5) ∨ p3)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60246219482735184877852597911 : (((False → True) → (((p5 ∨ ((((p1 ∨ p3) ∨ p2) ∨ (p3 ∨ (p3 ∧ (p2 ∧ True)))) ∧ True)) ∧ p5) → ((False ∨ (p3 → p5)) ∧ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h4
  -- Conjunctions on the left can always be decomposed.
  let h27 := h2.left
  let h28 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h37 =>
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387559624464704488209591186022 : (((((p2 ∨ ((p5 → (p5 → p1)) → ((p3 → (False ∨ p3)) → ((p4 ∧ (p4 → p2)) ∨ (p4 ∨ p3))))) ∨ (p4 ∨ (p3 ∧ p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_119475036104644703491382915174 : ((p4 → (False ∧ (p2 → (((True ∧ (p5 ∨ p2)) ∨ (p3 ∧ p1)) ∧ (False ∧ (True ∧ ((p1 → False) ∧ (p3 → (p5 ∧ p5))))))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324072860648232648485614803905 : (p5 ∨ ((((p2 → (p3 ∧ p4)) → ((p1 → True) → (p5 ∨ p2))) ∨ True) ∨ ((((p5 ∨ p4) ∨ (True ∧ p1)) ∧ ((True ∧ True) ∨ p5)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677081480444848285511538394239 : ((((p3 → (p4 → ((((True ∨ True) → (p5 → p3)) → (p1 ∨ (p4 → p1))) ∧ ((p4 ∧ p2) ∨ p5)))) ∧ (((p5 ∨ True) ∨ p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46304804007150283213460286235 : ((((p4 ∧ (p3 ∧ (p2 → (p3 → (p1 → (False ∧ ((False → ((p4 ∧ p2) ∨ p3)) ∧ p4))))))) → (p5 ∧ (True → p5))) ∧ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121730637807334091978887847553 : (((((p1 ∨ True) ∧ ((False ∧ False) ∨ p4)) ∨ ((False → p5) → (p5 → ((False → (p1 → (p5 → True))) → (p5 ∨ p3))))) → p2) → (p2 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ True) ∧ ((False ∧ False) ∨ p4)) ∨ ((False → p5) → (p5 → ((False → (p1 → (p5 → True))) → (p5 ∨ p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353379108087453204851405480318 : (p4 → (False ∨ ((((False ∨ True) ∨ True) → False) → ((p3 ∨ (p4 → (((False ∨ (p3 → (False ∨ p3))) ∧ (p1 → False)) ∧ (True ∨ p3)))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191057992270440427860713073604 : (((p1 ∧ (p2 ∨ (p2 → p5))) → ((p5 → False) ∧ p4)) ∨ (p3 → (p3 ∧ (((p3 ∨ p3) → p3) ∨ (((p1 → p2) ∧ (True ∧ p3)) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300953127295342865043822472078 : (False ∨ ((((p1 ∧ ((True ∨ (p5 ∨ (p5 → p1))) → p2)) ∧ p1) ∧ False) ∨ ((p4 ∧ ((p2 ∧ (p4 ∧ (p3 → False))) ∨ p5)) → (p1 ∨ True)))) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
theorem thm_5_vars_154280267540545033572517641454 : ((((p1 ∨ p1) ∨ (((p5 → ((((p4 ∧ (True ∧ p4)) ∨ True) ∨ p2) → p4)) ∨ p4) → p1)) ∨ True) ∧ ((False ∧ (p3 → p2)) → (p1 → p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867578768925913367496572663075 : (((((p4 ∧ p2) ∨ (((((p3 ∧ True) → (p3 ∧ ((p5 ∨ p4) ∧ ((False → ((p3 → True) ∨ p3)) ∧ True)))) ∧ p2) ∧ p5) ∨ True)) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p2) ∨ (((((p3 ∧ True) → (p3 ∧ ((p5 ∨ p4) ∧ ((False → ((p3 → True) ∨ p3)) ∧ True)))) ∧ p2) ∧ p5) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_64566396326598968545259820654 : ((p1 ∨ ((p5 ∨ (p2 → p3)) ∧ (((((p1 ∨ (p5 ∧ (True → p3))) ∧ p1) ∧ (p5 → p2)) ∨ (p4 → p5)) ∨ ((p4 → True) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697535770348696103442362409378 : ((((p5 ∧ (p3 ∨ (((p2 → p4) ∨ (True ∧ p2)) ∧ (p5 ∨ p2)))) ∧ (p2 ∨ (p3 ∨ ((((p4 ∧ (p3 → p3)) → p2) ∧ p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78633995459301103601518937735 : ((((((p2 ∨ (False ∧ ((True → (((p5 ∨ False) ∧ (p2 ∧ p4)) → p5)) → p2))) ∨ p1) → False) ∧ (True ∧ (p4 → p1))) ∧ (p2 ∧ p1)) → p4) := by
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
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 ∨ (False ∧ ((True → (((p5 ∨ False) ∧ (p2 ∧ p4)) → p5)) → p2))) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245057124407070544551836689337 : ((p1 ∧ p5) ∨ ((p1 ∨ (((p5 ∧ p3) ∨ ((p1 ∨ ((False ∧ p1) → (False ∨ p5))) ∧ (p3 ∧ p4))) ∧ True)) ∨ ((p4 ∧ p2) → (p3 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_57150250256349676455059523220 : ((((p5 → p3) ∧ p2) ∨ ((False → (p1 → p4)) → ((False ∨ p5) → (p2 → ((((p2 ∧ (p2 ∧ True)) → p4) → False) ∧ (p3 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89236417816984496772968322162 : (((p1 ∧ (p4 → False)) ∧ ((p1 → (False ∧ (p2 → p5))) ∧ ((False → ((p1 → ((p5 → False) ∨ p4)) → (p5 ∧ p3))) ∨ (p1 ∨ p4)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230647606896673776651672671219 : (((p3 → False) ∧ p3) → (((((p1 ∨ (p1 → p4)) ∧ (p5 ∧ (p4 ∨ p3))) → ((p1 ∧ p1) ∧ (p1 → ((p5 ∨ p3) ∧ p3)))) ∨ p5) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656669088120866060465518749260 : ((((((p2 → (p5 → (p1 ∨ p4))) ∧ p4) ∧ ((((((p2 ∨ p1) ∧ True) ∧ p1) ∨ True) ∧ (p4 ∨ (p2 ∨ True))) ∧ False)) ∨ (p1 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_342902591998529431313289422396 : (p2 → (((p5 ∨ p2) ∨ (p2 ∨ (p4 → False))) → (((True → (p1 ∨ p4)) ∧ (False ∧ ((((True ∨ (p5 ∧ p2)) ∨ p2) → p5) ∨ False))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59406009986776174841597045001 : (((True → p4) ∨ (((p1 ∧ ((((False ∨ (p5 → p1)) ∧ ((p3 ∨ (p3 ∧ p1)) ∨ p5)) ∧ True) ∨ ((False → True) ∨ True))) ∧ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737802798545381888010472082071 : ((((True ∧ False) ∨ (((True → ((p2 → False) ∧ ((((p1 ∧ p4) → (p5 → p2)) ∧ p4) → (p3 ∨ False)))) ∨ (p3 → p3)) ∨ (p2 ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116537128489629354929946010031 : (((True ∨ p5) ∧ (p5 → (((False → p2) ∧ ((((p1 → p5) → (p3 ∨ (True ∧ (False ∧ p1)))) ∧ p5) ∨ True)) ∨ (p4 ∧ p4)))) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354944365179779618711148159233 : (p5 → ((True → ((p4 ∧ ((p1 → (p2 → (((p1 ∨ (p1 ∨ ((True ∨ p2) → ((p3 → p4) ∨ p3)))) → p4) → p1))) ∨ p4)) ∨ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166511696387036020813330820773 : ((p4 ∨ (((False ∨ p4) → (p2 → (((p2 ∧ (p4 ∨ True)) → (p2 ∧ p3)) → p4))) → False)) ∨ (p3 ∨ (False → ((True ∧ p2) ∨ (p1 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178540446073425865355500656653 : (((False ∨ (True ∨ (p3 ∧ ((p4 ∧ p3) → p2)))) → ((p1 ∨ p2) ∨ p3)) ∨ ((((p1 → (p5 ∧ (True → p5))) ∨ p1) ∨ True) ∨ (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797257395861677318685531948303 : (((p1 → (((p5 ∧ ((p3 → ((((p2 → p1) → False) ∨ ((p2 → False) → p1)) ∧ (p2 ∨ p3))) → ((True ∧ p3) → False))) ∨ p1) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_684949391819202107574442380390 : ((((p2 ∧ ((p5 → p2) → (((p1 → p2) ∨ (((p5 ∧ p1) → (p4 ∧ p3)) → p5)) ∨ p2))) ∨ (p4 → (False → (p4 → (p4 → True))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112218601708595787619511058089 : (((p1 ∨ ((p1 ∧ (((True → p3) → ((p2 ∨ (p1 → ((True ∧ p4) ∧ p1))) ∨ p3)) ∨ ((p2 ∨ p1) ∧ False))) ∨ False)) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347660525028086216070882413123 : (p3 → (((p4 ∧ False) → (p1 ∧ p2)) → ((p5 ∧ (False → p3)) ∨ ((p5 ∨ (p1 → (p2 ∨ (((False ∧ False) ∨ False) → False)))) ∨ (p5 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755671709896364830067215876460 : (((p1 ∧ ((((((((p1 → (p2 ∧ True)) → False) → True) ∨ p5) → p3) ∨ (p1 ∧ p3)) ∧ (p4 ∧ (p4 ∧ ((p5 ∨ True) ∧ True)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115675196506103283244699904862 : (((False ∧ ((p2 → (p4 ∨ p3)) → False)) ∨ (p4 ∧ (((((p5 ∨ p4) ∧ (p1 → p4)) ∨ False) → ((p4 ∨ False) ∧ p1)) ∧ p3))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322505911940733214349391007341 : (p5 ∨ ((True ∧ (((False ∧ p4) ∧ ((p1 ∧ p2) → (((p4 ∧ (p3 ∨ p5)) ∨ True) ∧ p2))) ∨ ((p1 → ((p3 ∨ p5) → True)) ∧ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263086736946584051653737884742 : (True ∧ (((p3 → ((p5 → False) ∨ ((((False ∧ (p3 → ((p3 → p4) ∧ True))) ∧ (p3 ∨ (False ∧ p1))) ∨ p3) ∧ p4))) ∨ p3) ∨ (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38664113532155555530646946960 : (((((((p2 ∧ p5) ∨ p1) ∨ True) ∧ p2) ∧ (p2 ∧ ((p2 → p2) ∧ ((((p3 ∧ p5) ∨ p1) ∨ (p5 ∨ p3)) ∧ (False ∧ False))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64332629955819498587238893143 : ((p1 ∨ (((False ∨ False) ∨ ((True ∨ (p2 ∨ p4)) → ((p4 ∨ p2) ∨ ((False ∧ (False ∨ p1)) ∨ (((p2 → p4) → False) ∧ p5))))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350333039040579880667244598148 : (p4 → ((p1 → (((False ∧ False) → (((True ∨ True) ∨ ((True → ((p3 ∨ p4) → (((p5 ∨ p4) → p2) ∨ p1))) ∧ False)) ∨ p5)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114038802887061054793039161871 : (((((p3 ∧ ((((((p2 → False) → p5) ∧ p3) ∧ p3) ∧ p5) → (p4 ∧ p3))) ∨ p1) ∧ (False → p2)) ∨ (p1 → (p4 ∨ p1))) ∨ (p5 ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173521046736884004606049694063 : ((((p5 → (p2 ∧ (p5 → ((False ∨ p5) ∧ p3)))) ∧ (p5 ∧ (p2 ∨ p3))) ∧ p2) → (((p5 ∧ (p1 ∧ (False ∧ p5))) ∨ (p5 ∧ False)) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147134003402439381214918705051 : ((((p4 → p5) → (((True → (p1 ∨ p2)) → (p5 → p1)) ∧ ((p3 ∧ (True ∧ False)) ∨ (p3 ∧ p2)))) ∧ True) ∨ (False ∨ ((True ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180451209375689690838286383429 : ((((True ∧ True) ∨ (p1 → ((p3 → (True ∨ p1)) ∨ p2))) → (p1 ∨ False)) → ((((p4 ∨ p1) ∧ (p1 ∨ True)) ∧ (False ∧ p2)) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323906865968716929701343711759 : (p5 ∨ (((p5 → p5) → ((p5 ∧ ((True ∨ p2) ∧ p5)) ∨ (((p4 → False) → True) → p4))) ∨ (p4 ∨ ((p1 ∨ ((p3 → False) → True)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_3396513272567487941739572078 : ((p3 → p4) → (((((p3 ∧ ((p1 ∨ (p4 ∨ ((p1 → p4) → p4))) ∧ ((p2 ∨ True) ∨ p1))) ∨ p5) ∨ True) ∨ (p3 → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114481100442949317570197211367 : ((((p4 ∧ (p1 ∨ ((True → (False → (((p5 ∨ p3) ∨ False) → p3))) → p3))) ∨ (True ∨ p2)) → ((p3 → False) ∨ (True ∧ False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64761917623971936125332896979 : ((p2 ∨ ((p3 ∧ (p3 ∧ (p5 ∨ (((p5 ∧ p2) → p4) ∧ ((p5 ∧ False) → (p5 ∧ ((p1 ∨ (False ∨ p3)) ∨ (p2 ∨ True)))))))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706803440801646917057595299215 : ((((((True → p3) ∨ (p4 → (p2 → p3))) ∧ p2) ∨ (((p3 ∧ (p1 ∧ ((p5 ∨ p1) → False))) ∧ False) ∨ (True ∧ ((p2 ∧ False) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769901260951332347116348865649 : (((p5 ∧ (True → (((p2 ∧ (p4 ∨ False)) ∨ p1) → ((p2 ∧ ((p1 ∧ ((p4 → True) → p4)) ∨ ((p3 ∧ (p1 → False)) ∨ p1))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150008521217915703571365464341 : ((p5 ∨ (((p5 ∨ ((p1 ∨ p5) ∧ ((False ∨ (p2 ∨ (((False ∧ p5) → p4) → p4))) ∧ True))) ∨ p3) → p3)) ∨ (((p3 ∨ True) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40762085431520929642649472528 : (((((False → p5) ∨ ((((p4 ∧ (p4 ∨ True)) ∨ p4) → (False → (((p4 ∨ (p2 → (p1 ∨ True))) ∨ p2) ∧ p5))) ∨ p2)) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661962962324691246119259814630 : ((((((False ∨ p4) ∨ ((((False ∧ p5) ∨ (p3 ∧ p4)) ∨ (False ∨ p3)) → p5)) ∨ (p5 ∨ (False ∨ ((p1 ∧ p5) ∨ p2)))) → (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53093944037957525059030378754 : (((p2 ∨ (False → ((p4 ∧ (False ∧ True)) ∧ (p3 ∨ (p2 ∧ p3))))) ∧ ((((p4 → p1) ∨ p5) → False) ∧ (p1 ∨ (p1 → (p4 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53254361484375561448216648524 : ((((p4 ∧ p2) ∨ (p1 ∧ (p2 ∧ (True ∨ ((p4 → p2) → p4))))) ∨ ((p5 ∨ (((p3 ∨ (False → p1)) → (True ∨ p5)) ∧ p3)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254245686040002854196983879507 : ((p2 ∧ p2) → ((p5 → p1) → ((False ∧ (((((((p2 → p4) ∧ (p1 ∧ p1)) ∧ True) → p3) ∧ False) ∧ p4) ∨ ((p3 → True) → p3))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719221151832178503555783741684 : ((((p3 ∧ ((False ∧ p1) ∨ p2)) ∨ ((p4 ∨ (((((p2 ∧ ((p3 ∨ p1) → (p1 ∧ p3))) ∧ (p2 → p3)) ∧ False) ∧ p4) → p4)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147281956618576707001297562959 : ((((False ∧ (p5 ∧ (True ∧ (((p5 ∨ ((p5 ∧ p4) ∨ ((p2 ∨ p1) ∧ p4))) → False) ∨ p5)))) ∨ p3) ∨ True) ∨ (True ∧ ((False → p4) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166288524962304972681469723170 : ((p4 ∧ ((((False ∧ True) → ((p4 ∨ (False → True)) ∧ False)) → p2) ∧ (p1 ∨ (p3 ∧ False)))) ∨ (((False → p5) ∨ p4) ∨ ((p1 → True) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53388161927420510077301518508 : ((((False ∨ (p5 → ((p2 ∨ p4) ∧ ((p2 ∨ p3) ∨ p2)))) → p4) → ((((False ∧ p4) ∧ p1) ∧ (p1 ∧ p1)) ∨ (False → (False ∧ p3)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786548451186453647613807009649 : (((p4 ∨ ((((p5 ∨ p2) ∨ (p4 → (p5 ∨ p4))) ∧ (p2 → p5)) ∨ ((((p1 ∨ (p2 ∨ ((p2 ∨ p3) → p2))) ∨ p4) ∨ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746669681285921532358979956602 : ((((p3 ∨ p1) → ((p3 ∧ ((False → True) → p4)) ∨ ((p3 → (p2 → (((p5 ∧ p3) ∨ (p2 ∧ False)) ∧ (p5 ∧ p1)))) ∧ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145869820609594779416489830626 : (((p1 ∨ p4) → ((((p4 ∨ False) → (p4 ∨ p3)) → (p3 ∧ False)) → ((p5 ∧ True) ∨ (p4 ∨ (p5 ∧ False))))) ∧ (((p1 → True) → False) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∨ False) → (p4 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665606978637010292912045893471 : ((((((((p2 ∧ p1) ∨ p1) ∨ p3) ∧ (p1 → ((((p5 ∨ p4) ∧ p2) → (p1 → (False → True))) ∨ False))) ∨ p4) ∧ (False ∧ (True ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778190075273847788098409379601 : (((p1 ∨ ((p2 ∧ p2) → (((((p4 ∨ True) → p5) ∨ p3) ∨ False) ∧ (p1 → ((p5 ∨ p2) ∧ ((False ∨ p3) ∨ (p1 ∧ (p2 ∧ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217148124894873451451900422298 : ((((p3 → p3) ∨ p5) ∨ p3) → (p2 ∨ ((p1 → (False ∨ True)) ∨ (((p4 → p5) → p2) → (((p1 ∨ p5) ∨ p3) → ((p1 ∨ p4) → p1)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318915752141154338043244133919 : (p4 ∨ (((False → (((((((p4 ∧ (p3 ∧ (p3 ∨ p2))) ∧ p5) → False) ∨ (p3 ∨ p2)) ∧ p1) ∧ True) ∧ p2)) ∧ p5) → (p1 → (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203024482766883150981987652875 : (((p4 ∧ p3) → ((p2 ∧ False) ∨ True)) ∧ ((False ∨ ((((True ∧ (p3 → p2)) ∧ p1) → p3) ∧ (p4 ∧ ((p4 ∨ (False ∧ False)) ∧ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173972511704584771743400011365 : ((((p4 ∧ (p4 ∨ p5)) ∧ ((p3 ∨ True) ∧ ((p3 → p3) ∨ (True → False)))) → p3) → (((((p3 ∧ p4) ∨ (p4 ∧ p3)) ∨ p3) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48954438159225363113896271102 : ((((p4 ∨ ((p3 ∨ (p1 ∨ ((True ∧ (True → p2)) ∧ p2))) → (p5 ∧ ((p3 ∨ (False → p3)) ∧ p2)))) ∧ p2) ∨ (False ∨ (p1 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



