variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42089592376750750262642500632 : ((((p4 → p5) ∨ (((p5 ∨ ((p3 ∧ (p4 ∨ (p1 → p3))) ∨ (p2 → ((p5 ∧ (False → True)) ∧ (p5 ∨ p5))))) ∨ p2) → p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633912171589455886553678419216 : ((((((p4 → (((((True ∧ False) ∨ (p2 → (p4 ∧ True))) → True) → (p3 ∨ (p3 → (p4 ∧ True)))) ∧ p3)) ∨ p1) → (p5 ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301252424239345235360707944845 : (False ∨ (((p4 ∧ (p1 ∨ p2)) ∨ (False ∧ p4)) ∨ ((p4 ∨ (p5 ∨ (p4 ∨ ((p1 → False) → ((p2 ∧ (p3 ∧ (False ∧ p2))) → False))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617201147687762460255585131714 : ((((((p5 ∧ (True → p5)) ∧ ((p1 ∨ p4) ∨ p1)) ∨ (True ∨ (p1 ∧ (p2 ∨ (((False ∨ (True ∧ p3)) → p3) ∧ (True → p3)))))) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_793789394106738296092708462370 : (((True → (p1 → ((p3 ∧ p1) ∨ ((p4 ∨ p2) ∧ ((True → ((((p5 ∨ ((p5 ∧ False) ∨ (p1 → p4))) → False) ∧ p3) → False)) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692896326319302818019937398853 : (((((p5 ∧ p2) ∧ (((p2 ∧ p5) ∧ p3) → ((p3 → p2) ∧ (True ∧ p4)))) ∧ ((((False ∧ ((p4 ∧ False) ∧ False)) ∧ p4) → p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164026914150779523937383801364 : ((False ∨ (((p2 ∧ p3) ∧ (((True ∧ p5) → (p2 ∧ p5)) ∨ ((p1 ∧ p5) → p1))) → True)) ∧ (((((p5 ∨ True) ∨ p2) → p3) ∧ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118506158765754505168067754310 : ((p3 ∨ (((p4 ∨ p5) ∨ ((p5 → p4) ∧ p3)) ∧ (p2 → ((((p2 → (p5 ∧ p4)) → ((True ∧ p4) → False)) ∧ False) → p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613573843519083344027704154385 : ((((((p5 ∧ ((p5 ∧ (((p3 ∨ (p2 → p2)) → (p1 ∨ p1)) → p4)) → ((p4 ∨ p2) ∨ p5))) ∨ p1) ∧ ((p3 ∨ p2) ∨ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207612870714552414043555575711 : ((((True ∧ (p5 → p3)) → p4) → p1) → (((p5 ∨ p2) ∧ p3) ∨ (p3 → ((((p4 → (p4 ∧ (p4 ∧ p4))) → p4) ∨ p1) ∨ (p3 ∨ p2))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111652717639304521432233164334 : (((((p4 → p2) ∨ ((p5 ∧ p1) ∧ (((p1 → p4) ∧ p5) ∨ (p3 ∧ (p5 ∧ (((True → False) ∨ p1) → p4)))))) ∨ p5) ∨ p2) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606934818922673905111651990080 : ((((((p5 ∨ (((p1 ∧ (p4 ∨ (p3 → (((p5 ∧ p5) → p2) ∨ True)))) ∨ False) ∧ p2)) ∨ ((p4 → (False ∧ p3)) ∧ p4)) ∧ p3) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_157516292659298645650506289141 : (((p2 ∨ ((((p5 ∨ ((p3 → ((p4 ∧ False) ∧ True)) → p3)) ∨ True) ∧ p4) ∨ True)) ∨ (p4 → p1)) ∨ ((p4 ∧ (True ∨ p2)) → (p1 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116807168242274516646346289979 : (((p3 ∨ p2) ∨ (((((p5 → False) → (p4 ∧ p4)) ∨ p1) → p4) ∧ ((p3 ∧ (((p2 → p3) → p1) ∨ (p4 → p4))) ∧ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67646557439606320184436233562 : ((p1 → (p2 ∨ (((((False ∨ (((p1 ∧ (False → True)) ∨ (True ∧ False)) → p3)) ∧ ((False ∧ p5) ∨ p5)) ∨ False) ∨ p3) ∧ (p3 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55931937412346009505814114204 : (((p1 → (p2 → (p3 ∧ p2))) ∧ ((p3 ∧ ((((p2 → (p1 ∧ p1)) ∧ (p4 → p2)) ∧ (p4 ∨ (p5 ∧ (p1 → p1)))) ∨ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173231694657470141725318365558 : ((True → ((((p5 ∧ (True → (False → p4))) → (p1 → p3)) → (p3 ∨ p2)) → p5)) ∨ (p5 ∨ ((False ∧ (False ∨ (False ∨ (p1 ∧ p2)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_46985651785173916933742329092 : (((((p1 → (p4 ∨ (((p4 ∨ p4) ∧ ((p2 ∧ (p2 → (True → p1))) → True)) → p5))) → ((p3 ∧ p4) ∧ p2)) → False) ∨ (False → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40914605820123964363980000498 : ((((p2 ∨ ((p1 ∨ (p5 ∧ (p4 ∧ True))) → ((((p4 ∨ (p5 ∨ p5)) → p2) ∨ (False → (False → p1))) → False))) ∧ (True ∨ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311937314284807232385102902758 : (p2 ∨ (p3 ∨ (((False ∨ False) ∧ ((False ∨ (((p4 → p2) → p3) → p1)) ∨ (((p1 ∨ p3) ∨ False) → (p1 → (False → True))))) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165065754959311209347536284017 : (((p2 ∧ (((p3 ∨ p5) ∨ (p2 ∧ (((p5 ∨ (False → False)) ∧ p5) ∧ p2))) → False)) → False) ∨ (((True ∨ p1) → (p5 → True)) ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113580034252915380237194908914 : (((p1 ∧ (((True → ((p4 → True) ∧ (((True → (p4 → (p5 ∧ p3))) ∨ False) ∧ (p3 → p2)))) → p3) → False)) ∨ (True ∨ p5)) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683316568803114011208568681710 : ((((p3 ∨ ((False ∧ (p4 ∨ p1)) ∧ (p2 → (p4 → (False ∧ ((p2 ∧ (False ∧ p2)) → True)))))) ∧ ((p5 ∧ p1) ∧ ((p3 ∧ p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111922250121424062498266718345 : (((((((p3 ∨ p5) ∨ (False → True)) ∨ True) ∨ ((p2 ∧ p5) ∧ p5)) → (((p5 ∨ p4) ∨ p3) ∨ ((p3 ∧ p3) → p3))) ∨ p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206965249628140165453197004946 : ((((True ∨ (p3 ∧ p2)) → p4) ∧ p3) → (p3 ∧ (((p5 ∨ ((p5 ∨ True) → ((p5 → p1) ∧ p1))) ∨ p3) ∧ ((p4 ∧ p1) → (False → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786348409173205565682209697315 : (((p4 ∨ (((((False → (((True → p2) ∨ p4) → p5)) ∧ p4) ∧ (True ∧ p1)) ∨ (p1 ∧ p2)) ∨ ((p2 ∨ p3) ∨ ((p4 ∧ False) → p4)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61822694169843136722668334495 : ((p2 ∧ (((True → p2) → ((p1 ∨ p4) ∧ (p4 → (((True ∨ ((((False ∧ True) → p4) ∨ p1) → (p2 → True))) ∨ p5) ∧ p2)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231384991461544754671189132492 : (((False → p5) ∨ p3) → (p2 → ((p2 → ((True → p3) ∨ p5)) ∨ (((True ∧ True) ∨ (((p4 → p2) → (False → False)) ∧ p3)) ∨ (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320421471643910768694290056287 : (p4 ∨ ((True ∨ p4) → (((p3 ∧ (True ∨ p3)) → (True → ((p1 ∨ ((p1 ∧ ((p2 → True) → (p1 ∨ False))) → p3)) ∧ p1))) ∨ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_136203765311422937789209709021 : (((p1 ∨ ((p4 → (p4 ∧ False)) ∧ p2)) ∧ (p2 ∧ (((True ∧ p3) → False) → (False ∧ ((False ∨ (True ∨ False)) → p1))))) ∨ (False → (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138436209955633167461942424968 : ((p5 → (((p4 ∨ (p3 ∨ p3)) ∧ (((p5 ∧ p3) ∨ p4) ∨ False)) → ((p4 ∨ ((p5 ∨ p1) → p1)) → (p5 → p4)))) ∨ (p2 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115460594808481320245823132561 : (((True ∧ (False ∧ (p3 ∨ ((p5 → False) ∨ False)))) ∨ (((True ∨ p2) ∧ (p1 → (False ∨ True))) ∨ (p5 → ((p5 ∧ False) ∧ True)))) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172154264105256085693985101821 : ((((p5 → (p1 ∨ (((p3 ∨ p4) ∧ True) ∧ p3))) ∧ p4) ∨ ((p3 → p2) ∨ True)) ∨ (((((p1 ∧ p5) ∨ (p3 ∧ p5)) ∧ p5) → p3) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40819311693994644703363753891 : ((((p5 ∨ (((((p4 ∨ ((False ∧ p3) → False)) ∧ (p2 → (p5 → p2))) → ((p1 ∧ (False ∨ p3)) ∧ p4)) → p1) ∨ p4)) → p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172771803711571984612908863289 : (((p2 ∨ True) → (p4 ∧ ((p3 ∨ (((p5 ∧ p4) → True) ∧ (p5 ∨ False))) ∨ False))) ∨ (p2 → (p4 → ((p1 ∧ p4) ∨ ((p1 → p4) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157952141629929571548046056275 : ((((((p2 → (True → p5)) ∨ p5) → False) ∧ p2) ∨ (False → (p5 ∨ (p3 ∧ ((p3 ∨ p1) ∧ p4))))) ∨ (((p1 ∨ (False ∧ False)) ∧ True) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41124724241045086226779429548 : (((((((p2 ∧ False) ∨ (((True → (p2 ∧ (p3 → (True → p5)))) ∨ p2) ∧ False)) ∨ (True ∨ p5)) ∧ p5) ∨ (p4 ∨ (p2 → True))) ∨ False) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322630379870536093028351160415 : (p5 ∨ ((((((p1 ∧ (False → p2)) → (((p2 ∧ (p2 → False)) → p3) ∧ (p5 → p1))) ∨ (p2 ∨ (p5 ∨ (True ∧ p1)))) → p2) ∧ p3) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ (False → p2)) → (((p2 ∧ (p2 → False)) → p3) ∧ (p5 → p1))) ∨ (p2 ∨ (p5 ∨ (True ∧ p1)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138138967595799137132136952260 : ((p1 → ((((p5 ∨ ((False ∧ (p5 → ((p2 → p1) ∨ True))) ∧ ((p2 → (p4 ∨ True)) → False))) ∧ p1) ∧ False) ∧ p3)) ∨ ((False → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117020996038044797616443094311 : (((p1 ∨ p5) → ((((True → p3) ∨ (p5 → ((False → p1) → (p1 ∧ (p2 ∨ (p5 ∨ (p2 → True))))))) ∧ True) ∨ (p1 ∨ p3))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207726807798299453099144068869 : (((p3 ∧ ((False → False) → p3)) → p2) → (((True ∧ True) → (((p2 ∨ p5) ∨ ((p1 → p5) ∨ False)) ∧ p2)) ∨ (p4 → (p3 → (True ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757173600370303645217376001762 : (((p1 ∧ ((p1 ∧ (True → False)) → (p3 ∧ (p2 → ((p2 ∨ ((False → p2) → p3)) → (p5 ∨ (((p3 ∧ (False ∨ True)) ∧ False) ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702376726365607782660472613445 : ((((((p2 → ((p1 → (p3 ∨ False)) ∨ True)) → False) ∨ p1) ∨ ((p3 ∨ ((((p5 → p5) ∧ p1) ∨ (p5 → p2)) → p2)) → (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215225910380742486092265969956 : ((False ∧ ((p2 → p1) ∧ p3)) ∨ (((p2 ∧ p1) ∨ ((p3 ∨ ((True ∨ p4) ∨ p5)) → ((p4 → (False ∨ (p3 → (p5 → p2)))) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40421620835068265823795944007 : ((((((False ∧ p2) ∧ ((((p4 → ((p2 ∨ p3) ∧ False)) ∨ True) ∨ True) ∧ p3)) ∨ ((p3 ∨ p1) → ((p3 ∧ p1) → True))) ∨ True) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41144261248972484250855412179 : (((((((p2 ∨ p3) ∧ p2) ∨ (p1 ∨ (p1 ∨ (p4 ∧ True)))) → (p1 ∧ ((p5 ∧ (p5 → p3)) ∧ p5))) ∨ (p5 → (p5 ∨ p2))) ∨ p1) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57733892949692119792387954833 : ((((p3 ∨ p2) → p3) → ((((p3 → False) → (p3 ∨ ((p5 ∨ p5) → p3))) ∧ (p1 ∧ (p1 → (((False → p5) ∧ p1) → p3)))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178672352831951154470776307800 : (((p5 ∧ ((p2 ∧ p3) ∧ p5)) ∧ (((p4 → p3) ∨ (False ∨ p5)) → p1)) ∨ ((p3 ∧ (p2 → (False ∨ (p4 ∨ p4)))) ∨ (p4 → (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164695815217740880563248199708 : ((((((p3 ∨ (False ∧ p4)) → ((p3 → (False ∨ p1)) ∧ (p3 ∨ p3))) → p2) ∨ p3) ∨ True) ∨ (p4 → (p2 ∧ ((p1 ∨ p2) ∧ (p4 → False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322538302474615791367880212927 : (p5 ∨ ((p5 ∧ (((p2 ∨ ((p4 ∧ (((p5 → p5) → (True → p2)) ∧ (p5 → p4))) ∧ ((p5 ∨ True) ∨ (True → p1)))) → True) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157375510474817907493013040824 : (((p5 → (p2 ∧ (True ∨ ((False → (p3 ∨ p5)) ∨ (p1 ∨ ((True ∧ (p2 ∨ p2)) → p3)))))) → False) ∨ (p1 → ((p2 ∨ (p3 → p1)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210326781586300879381537624131 : (((p2 ∧ (p5 ∧ p3)) ∨ True) ∧ ((p2 ∨ ((p4 ∨ (p5 ∨ (True ∧ ((p1 → p5) → True)))) ∨ ((p5 → (p5 ∨ p1)) → (p1 ∧ p3)))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120692368459065723953754462852 : (((((p1 → ((False ∨ ((p4 ∨ p2) → p3)) ∨ p2)) → (((p2 ∨ (p5 ∨ (p1 ∨ p5))) ∧ p5) → False)) ∧ (p2 → p1)) ∨ p3) → (p3 ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254270436893509902782407596168 : ((p2 ∧ p3) → (((((((False → p4) ∧ p1) → ((((p2 ∧ False) ∧ (p4 → p2)) → True) ∧ False)) ∨ p1) → p2) → ((p2 ∨ p1) ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_113277212802940960490465934549 : ((((((True ∨ True) → (True → False)) ∧ (True ∨ ((p4 ∧ (p5 ∨ p4)) → p5))) → ((p4 ∨ p2) ∧ (p2 ∧ p5))) ∧ (p2 → True)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116982070109912536456484195442 : (((p5 ∧ p1) → ((p4 ∨ (p5 ∨ (False → p5))) → ((True → False) → ((p5 → (p1 ∨ p3)) ∧ (p5 → (p1 ∧ (p4 → p3))))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160679519296660472886807238171 : ((((False ∨ (((p5 ∧ False) → p2) ∨ p4)) → p3) ∧ (((((p3 → p5) ∨ p5) ∧ False) ∧ p3) → p3)) → (p2 → (p5 → (True ∧ (p3 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ (((p5 ∧ False) → p2) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351360927608045552860739166103 : (p4 → ((((p5 → p2) → (p4 ∧ (p1 ∧ (p2 → p3)))) ∨ (p4 → ((p4 ∨ (p1 → p5)) ∧ (False → p3)))) ∧ (((p3 ∨ p1) → p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179410030814908309138907854178 : ((p4 ∨ ((((p5 → ((True ∨ p5) → p2)) ∧ True) ∧ (p3 → p5)) ∧ p4)) ∨ ((p2 ∨ (p1 → ((p4 ∧ p3) ∨ (p2 → p2)))) ∨ (p4 ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320130632925451904218936189108 : (p4 ∨ ((p5 ∨ (p5 → p5)) → ((p5 → ((p1 ∧ ((p4 ∨ (((p4 ∧ (p3 ∧ p5)) ∨ (p3 ∨ (p5 ∨ True))) ∨ p2)) → p1)) ∨ p5)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56529943690298758784596584995 : (((True ∨ (p2 → (False ∧ p3))) → ((p3 → p2) ∨ (((p4 ∨ False) ∨ ((p5 ∧ p4) → (((True ∨ p5) → True) ∨ p5))) ∧ (p2 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304711632646771449088881165120 : (p1 ∨ (((p3 → ((p5 ∨ ((p5 ∨ p1) ∧ ((p4 → ((p5 → ((p1 ∧ True) → True)) → p4)) ∨ p5))) ∧ p5)) ∨ (True → p5)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259066637556711891977048473778 : ((True → p5) → ((((True ∨ ((p1 → p4) ∧ (p1 ∧ ((p3 ∧ (p2 ∨ p4)) → False)))) ∧ ((p1 ∨ p3) ∨ (True → (p2 ∨ p2)))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618203416139333541425093863587 : ((((((p1 ∧ (p2 ∧ False)) ∧ p5) ∨ ((((((p3 ∧ True) ∧ (p5 ∨ p5)) ∨ p3) → p3) ∧ p4) ∧ ((p3 ∨ False) → (p2 ∨ p5)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_204681302694037250785448867241 : (((p1 ∨ ((False ∨ False) ∧ p1)) ∨ p1) ∨ ((((p3 → ((p4 ∨ False) ∨ True)) ∨ p2) ∨ p5) ∨ ((p2 ∧ ((p2 ∨ p4) ∧ p3)) → (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716599674504802231469434541881 : (((((True ∧ p1) → (p3 ∨ True)) ∧ ((p5 → (((p2 ∧ False) → p4) → ((((p5 ∧ p5) → ((p3 → True) → p3)) → p2) ∨ True))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323424116551263975459673779844 : (p5 ∨ ((((p3 ∨ (p3 → True)) ∧ (((False → False) ∧ ((((p5 ∨ False) ∨ p2) → p1) ∨ p1)) ∧ p2)) → (p5 ∨ p1)) ∧ ((True ∨ p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 ∨ False) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : ((p5 ∨ False) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225256539739309602766089172570 : (((True ∨ False) ∧ p4) ∨ (p4 ∨ ((True ∨ (p5 ∨ (p4 ∧ ((((False → ((False ∨ True) ∧ p5)) ∨ p3) ∧ p5) ∨ False)))) → ((p1 ∧ False) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256043057240574728594479456530 : ((True ∨ p4) → (((((True ∨ True) → (p3 → True)) ∧ p4) ∨ (((p5 → p3) ∨ (p2 ∨ (True ∧ ((p2 ∧ p4) ∧ False)))) → False)) ∨ (p5 → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190462914337959378418453322886 : (((((p3 → ((p5 ∨ True) ∧ p2)) ∧ p1) ∧ p1) → False) ∨ ((True ∧ (p3 ∧ p5)) → (((((p4 ∧ p5) ∨ p5) ∧ p1) ∧ (True → p2)) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738038881964958664565359923486 : ((((False ∧ True) ∨ ((((p2 ∨ True) ∨ (p5 ∨ ((p3 → False) → (((p3 ∨ p4) → p2) → (p4 ∨ (p1 ∧ False)))))) → p3) ∨ (False ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55225764776862501415092125515 : (((((p2 ∧ True) ∧ p4) → (True ∧ p5)) ∨ (p4 → ((False ∨ (((p1 ∧ True) ∧ ((((True ∧ p2) → p2) ∧ True) → False)) ∧ p4)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251418768391293198346350369572 : ((p2 → p5) ∨ ((p2 ∨ ((((((False ∨ (p5 → p5)) → (p3 ∨ False)) ∨ p5) ∨ p2) ∨ p3) → (p5 → (p5 ∧ (p4 → (p2 ∨ p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314554222667612065901985838931 : (p3 ∨ (((p2 ∧ p5) ∧ ((p5 → ((p1 → True) ∧ ((False ∨ ((p3 ∨ p1) ∧ p1)) ∧ p3))) → p1)) ∨ ((p4 ∧ p2) → ((p2 ∧ False) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88175497940664298133525328930 : ((((p1 ∨ True) → (p2 ∧ p5)) ∧ ((((((((p2 ∨ (p5 → p1)) ∨ False) → p1) ∨ (False ∨ p2)) ∧ p2) ∧ (p2 → p4)) ∨ p4) → p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54930794184120493318543405808 : ((((True ∨ ((p5 → p3) ∨ p4)) → p4) ∧ ((((((False ∨ False) → p1) → (p3 → (p4 ∧ ((p1 → p2) ∧ p2)))) ∧ p3) ∧ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46723633012308519292238619336 : (((True → ((p3 → ((False ∨ ((((p2 ∧ p2) ∨ (p2 ∧ (p2 ∨ (p3 ∨ (p5 ∧ p2))))) ∧ p1) ∧ p1)) ∨ p1)) ∧ p1)) ∧ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110769110014854520946980780160 : ((((p2 → (((p5 ∨ p5) → ((p1 ∨ (p3 → ((p5 → p1) ∨ p2))) ∨ (p3 ∨ (True ∧ (True → p3))))) → p5)) ∧ p3) ∧ p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712771660324192320425979331486 : (((((p5 ∨ p1) ∨ (p4 ∧ (True ∨ p1))) ∨ (p2 ∧ ((((p1 ∨ (p5 ∧ (p1 ∧ (p4 → True)))) ∨ p5) → p4) ∨ ((True ∧ p4) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147151888180708951057493553374 : (((p2 ∧ (True → (p5 ∨ (((True ∨ p3) ∨ ((p3 ∨ False) ∧ p2)) → ((p2 ∧ p2) → (p1 ∨ p4)))))) ∧ p1) ∨ (p1 → (True ∨ (p3 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137952299229030745454871590592 : ((p5 ∨ ((p4 ∨ (False ∨ ((p2 → True) → (((p5 ∨ True) ∨ p5) → (((False ∧ (False ∧ p5)) → p5) ∧ p4))))) ∨ True)) ∨ (p2 ∨ (p5 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179305097063213748699605129807 : ((False ∨ ((p4 ∨ (p4 ∧ ((True → p4) ∨ False))) ∨ ((p1 → p3) → p3))) ∨ ((True ∨ (True → ((p5 ∨ ((p1 ∨ p4) → p4)) ∧ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3914047114605370558369953341 : (False ∨ (((((p2 ∨ p3) ∧ (True → (((p4 ∧ p2) ∨ (p2 → (p5 ∨ (True ∧ p4)))) ∨ p1))) → p3) ∨ (p5 ∨ True)) ∨ (True → p4))) := by
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
theorem thm_5_vars_164691723839617049944884874114 : (((((p3 ∧ ((((True ∧ p2) ∧ (False ∨ (p4 → p5))) ∧ p1) ∨ True)) ∧ p1) ∨ True) ∨ p1) ∨ (p1 ∨ (((False ∨ (True ∨ p1)) → p1) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652362926302247031227977841584 : ((((p4 ∧ ((((p1 → True) ∧ (p5 → (p5 ∧ False))) ∧ ((False → p2) → p5)) ∨ (p1 ∨ (((False ∨ True) ∨ True) ∧ False)))) ∧ (False → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136233794218012891384446735237 : (((((p2 ∨ False) → p3) → (p2 → p1)) ∨ ((((p3 ∨ (((p1 ∨ True) ∨ True) → (p3 ∨ p3))) ∧ p1) → p4) ∧ p4)) ∨ (True → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254450727673289555808850167911 : ((p3 ∧ True) → ((((p1 ∨ (False ∨ (p1 ∨ p1))) → (True → (((p3 ∨ p5) ∧ p2) ∨ ((((p5 ∧ False) ∨ p3) ∨ p3) ∨ p4)))) ∧ False) ∨ p3)) := by
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
theorem thm_5_vars_721062285409489159104888701565 : (((((p4 ∧ p1) ∨ (p1 → False)) → ((p1 ∧ (p1 ∧ (p1 ∨ p5))) ∨ (p1 → (((False ∨ p3) → ((True → (False ∨ True)) ∨ p4)) → p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62653967375549401563435026107 : ((p4 ∧ ((((p3 ∧ ((p4 ∧ (((p2 → (p4 → False)) → p2) ∧ p5)) ∨ False)) → (False → (False → (True ∨ (p2 → p3))))) → p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107693465799599053069053354124 : (((False → p3) ∧ ((p1 → (True ∧ ((p1 → ((p3 ∨ p5) ∧ p3)) → ((((p3 ∨ p4) ∧ (p3 → p4)) ∨ p3) ∨ p4)))) ∧ True)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314589132949040054074382463775 : (p3 ∨ ((((p5 → (True ∨ p2)) ∨ True) → (False ∨ (False ∧ (False ∨ ((p5 ∨ p5) ∨ (p1 ∨ p3)))))) → (((p4 ∧ p5) ∨ (True ∧ p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (True ∨ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118817127572605368555047364749 : ((True → ((p3 ∨ (((p1 ∨ p4) → ((p5 → (p5 ∧ ((p4 → True) ∧ p3))) ∨ (p4 → p5))) ∧ ((p1 → p4) ∨ True))) ∨ True)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305033057769994990176010010679 : (p1 ∨ ((p4 ∨ (((p4 → (p5 ∨ ((p4 ∨ True) → ((p1 ∨ p1) → (p3 ∨ (False ∨ (p1 ∧ p3))))))) ∧ p4) → p1)) ∨ (False → (p4 → False)))) := by
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
theorem thm_5_vars_351389866968126484768035233483 : (p4 → ((((True ∨ ((True ∨ (p5 ∨ (False ∨ (p5 → True)))) → (p4 ∨ (p1 ∧ (True ∨ p5))))) → p5) ∨ p2) ∨ (((p4 → p5) → p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303867722222210305564805172083 : (p1 ∨ (((p5 → ((p2 ∨ (((True ∨ (p4 ∧ p5)) → p5) ∨ (True ∨ p5))) ∧ (((p5 ∧ p3) ∧ False) ∨ p4))) ∨ ((False → p3) ∨ p2)) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313060508935241247679509383429 : (p3 ∨ (((p5 ∧ ((p5 ∧ (((p1 ∧ False) → (p5 ∨ ((False ∧ p3) → p3))) ∨ (((True → (p4 ∧ p1)) ∨ p4) ∨ True))) ∧ p2)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303467076629493200064173263745 : (p1 ∨ (((((p3 → (p1 ∧ False)) → (p5 → (p2 ∧ ((p4 → p1) ∧ False)))) ∨ (False ∨ True)) ∨ (((p2 → (True → p2)) ∧ p4) → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_40241648107897347097307582604 : ((((p4 ∧ (p3 ∨ (p5 ∧ (p5 ∨ (((False ∧ p5) → (p4 ∧ p3)) → (((p2 ∧ (p2 ∨ p1)) ∧ (True → False)) ∧ p3)))))) ∧ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786513351578236893352066756529 : (((p4 ∨ (((p3 ∧ p5) → (p2 → ((p5 ∨ (p1 ∧ False)) ∨ (p2 → p2)))) → (True → (((p5 → (p4 ∨ (p2 → True))) → False) → p1)))) ∨ p1) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p4 ∨ (p2 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703876594658970133935998852927 : (((((((p1 ∧ p5) ∧ p2) → ((p2 ∨ False) → p1)) ∨ False) → (False ∧ (((p2 ∧ p1) → ((False ∧ p2) ∧ (p4 ∨ p3))) → (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



