variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157692288456631908501600452444 : (((p5 → ((False ∨ (p2 ∧ (p3 ∧ ((p1 → p2) ∨ p1)))) ∨ (p2 ∨ p3))) ∨ ((p2 ∨ p3) ∨ True)) ∨ (p1 ∧ (((p5 → p2) → p1) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707616035484914355014096365302 : (((((True → p4) ∧ (((p1 ∧ False) ∨ p3) ∨ True)) ∨ (False ∨ (((p3 ∧ ((p2 ∧ (p1 ∧ p2)) ∨ (p1 → (p1 → p2)))) ∧ p1) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_44723236356470719825629428143 : ((((((False → p3) ∨ p5) ∧ False) ∨ (p4 ∨ (((p2 ∨ ((True → p1) ∧ p4)) ∨ p1) → ((p3 → (False ∧ p3)) ∨ (p1 ∧ p3))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197378782969017970936157212304 : (((p1 ∨ ((p4 → True) ∨ (p4 ∨ p3))) → False) ∨ (((((p2 → p5) ∧ False) ∧ p2) ∨ p5) ∨ (((p4 → False) → (p2 → p2)) ∨ (False → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62501328739569436638083984829 : ((p3 ∧ (p1 ∧ (((True → p3) → (((p3 ∨ True) ∧ (p4 ∨ p2)) ∨ (True ∨ p4))) ∧ (((p3 → p5) ∧ p2) ∨ ((p4 ∨ p4) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621979725718603665579171985077 : ((((p1 ∧ (p4 → (((p1 → (p4 ∧ ((p2 ∧ (p1 → p4)) ∧ (p1 → ((False ∧ (False ∨ p1)) ∨ p1))))) → p5) ∨ (p4 → p5)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669995103724580772122639079530 : (((((((p2 → (False ∧ (p4 ∨ False))) ∧ p5) ∧ p3) ∧ (p2 → (p5 ∧ ((((p3 → p3) → False) ∧ True) → p1)))) ∨ ((True ∧ True) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307231167349917605094674953420 : (p1 ∨ (p1 ∨ (p2 → ((((p3 ∧ (p1 ∧ p3)) ∧ (p2 ∨ ((p4 ∧ True) ∧ p2))) ∨ ((p3 ∧ (True ∧ False)) → p5)) ∨ (p4 ∨ (p4 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329657321150732995628124651 : ((((True ∨ p4) ∧ p2) → (((((p5 ∨ p3) → p5) → ((p2 ∧ (p3 → p3)) ∧ p3)) ∨ (True → ((True ∨ True) ∧ p2))) ∨ False)) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227001978023318621513743381042 : (((p1 ∨ p3) → False) ∨ ((False → p2) → (((((p4 ∨ False) ∨ (p4 ∨ (True ∨ True))) ∧ (p4 ∨ ((p3 ∧ (False ∨ p3)) ∨ p4))) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49040897345454486687249094535 : ((((p3 ∨ (((p3 ∧ (((p1 ∨ (p2 ∨ ((p2 ∧ False) ∨ True))) ∨ p5) ∨ False)) → (False ∨ False)) → p3)) → p1) ∨ (False → (p2 ∧ p3))) ∨ p5) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115004501453363784600002089866 : ((((True ∧ (p5 ∨ p5)) ∧ (((True ∨ p5) ∧ (p5 ∧ p5)) ∧ p2)) ∧ ((p5 ∧ p1) ∧ (((p4 → True) → (False ∨ False)) ∨ True))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138433757675716062281871917988 : ((p5 → ((((p2 → (p3 ∧ False)) ∧ p4) ∧ (False ∨ (p1 ∧ (p5 ∧ p1)))) ∨ (p5 ∨ ((p1 ∧ p2) → (p5 ∨ p2))))) ∨ (p1 → (True → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738401610442367002082142441089 : ((((p1 ∧ p1) ∨ (((((p3 ∧ p3) ∨ False) → (p5 ∧ p2)) ∧ p4) → (p1 ∧ ((((True ∨ p4) ∨ p4) ∧ ((p1 ∨ p1) ∨ p2)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624562802527033315355046959224 : ((((p4 ∨ ((p1 ∧ (((p2 → p1) ∨ ((((p3 ∧ (p2 ∧ False)) ∨ (False → p3)) ∨ (True ∨ p2)) ∧ p1)) → p5)) → (False ∧ p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248347357937386501725314142758 : ((p2 ∨ p3) ∨ ((p2 ∧ (False → (p2 → False))) → (((p2 ∧ (p5 → False)) ∨ p4) ∨ (((((p5 → p2) → p2) ∨ p1) ∧ True) ∨ (p4 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199226054860389671094372685416 : (((p5 ∨ ((p3 ∧ (p2 → p1)) ∧ p4)) ∧ p3) → (((((p1 → False) → (p4 → p3)) → p4) ∨ ((p3 ∨ True) ∨ False)) ∨ ((True ∨ p5) ∨ p3))) := by
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
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330468662028909031693226581427 : (True → (p3 ∨ (p3 → ((((((False → p5) → (p1 ∨ ((p3 ∧ (p1 ∧ p2)) ∨ p5))) → (p1 → False)) ∧ p1) ∨ True) ∨ (p2 ∧ (p2 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41512390676851177919298392580 : ((((((((p5 ∧ p3) ∨ True) → (p2 ∨ p2)) → p4) ∨ p1) ∧ (p4 ∧ (p5 ∨ ((p1 ∨ p1) → ((p1 → (p2 ∨ False)) ∨ p5))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232885739167716083333075909435 : ((p3 ∧ (True ∧ p3)) → ((p4 ∨ (True ∧ ((((p2 ∧ (p3 → True)) ∨ p1) → ((p4 → (p5 ∧ p4)) ∧ False)) → ((p2 ∨ False) ∨ False)))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299388723549133142921245975942 : (False ∨ ((True ∧ (((((p4 ∨ p3) ∨ ((p3 ∨ p3) ∨ (False ∧ (p2 ∧ ((True ∨ p3) → (True ∨ (p5 → True))))))) → p5) ∨ True) ∨ p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714615712133516121291853114800 : (((((p1 → p1) ∨ (False → (p1 ∧ p4))) → (p5 → (((False ∧ p2) ∨ ((p2 ∧ p3) ∧ ((True ∨ False) ∧ False))) ∨ ((False ∨ p2) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178958747580464316371292397697 : (((False ∨ p5) ∨ ((((p5 → p1) ∨ (p3 ∧ p2)) ∨ p5) → (False ∨ True))) ∨ (((False ∨ (True ∨ p5)) → p2) ∨ ((False ∨ p1) → (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354115564962964677169989913085 : (p4 → (p5 → ((p4 → False) → (((p1 ∨ (p2 → ((True ∨ (True ∨ p2)) → ((False ∨ ((p4 ∨ (False ∧ p1)) → True)) ∨ p5)))) ∧ p2) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185451253629708173997266719599 : ((False ∨ (p3 ∨ (((p3 ∨ p2) ∧ p4) ∨ (True ∨ (p1 ∧ p1))))) ∨ ((True ∨ (True → p3)) ∧ ((p2 → (p3 ∧ p1)) ∨ ((p3 → True) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_245710014919709025105978673948 : ((p3 ∧ p2) ∨ ((False ∨ ((((p5 ∧ ((False ∧ False) → (False ∨ p4))) → (p1 → (p1 → ((p1 ∨ False) → p3)))) → p1) ∧ (p3 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112905390606750876999671649227 : ((((p3 ∧ p3) ∨ (((p4 → (((p4 ∨ p3) ∧ p4) ∨ p3)) → (((True ∧ p5) ∧ p4) → True)) ∧ (p5 → (False ∧ p1)))) → False) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755761131619827998670509973980 : (((p1 ∧ ((p2 ∧ ((((p4 ∧ p5) ∧ ((((p2 → False) → p3) → p1) ∧ p5)) ∨ ((True ∧ False) → (p3 → p2))) → (p2 ∧ p3))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329344369451078031426782203777 : (True → (((False ∧ p1) → p1) → (((p1 ∨ ((((((p1 ∨ False) ∨ False) ∨ ((p4 ∨ (p5 ∧ False)) ∨ p4)) ∨ p2) ∨ p1) ∨ p5)) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192580215621541728402706059289 : (((True → (p4 ∨ (p5 → (p5 ∨ (p4 → p3))))) ∨ p5) → (False ∨ ((p4 ∧ ((p4 → (p3 ∧ p3)) → p4)) ∨ (True ∧ (p5 ∨ (False → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337105597879365034122765930273 : (p1 → (((p5 ∨ (p4 ∨ p4)) ∧ ((p3 ∨ (((((False → p1) ∧ p4) → (p1 → p3)) ∨ False) ∧ p5)) ∨ (True ∨ (False ∨ p4)))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112681744735270375757679987367 : ((((p4 ∨ ((p5 ∧ (p1 ∧ (p2 → (((False ∨ (False ∧ (p1 ∧ p4))) ∨ p4) ∨ True)))) ∧ p1)) → (p2 ∨ (p1 ∨ p1))) → p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609595016783034230639481608181 : (((((p5 ∧ (((p5 ∨ ((((p1 → (False ∧ True)) ∧ (p2 → True)) ∧ (p2 ∨ (False ∨ p4))) ∧ p5)) ∨ p2) ∨ (p1 → True))) ∨ True) ∨ p1) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_261031940320607517838292110308 : ((p4 → p2) → ((((p1 ∧ ((True → False) ∧ (p4 → (p3 ∧ p1)))) → p5) → (p5 → p1)) ∨ ((((p1 ∨ (p1 → p1)) → p1) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41471148600527869843502841070 : ((((((True → p4) → ((p5 → p3) ∨ ((p2 ∨ p1) → p3))) ∨ p5) ∨ (((False ∨ ((p1 ∧ p5) ∨ p2)) → (p1 → p4)) ∨ p4)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320458658382899291427228369825 : (p4 ∨ ((True → p1) → (((p1 → False) ∨ p3) ∨ ((((((((p5 → True) → True) → (p2 ∨ (p4 → p5))) ∧ p5) ∧ p2) ∨ p5) → p5) ∨ False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341033671997153092000369491658 : (p2 → ((p5 ∧ (p3 ∧ ((p1 ∨ ((p2 ∧ (p1 ∧ (p1 ∨ p5))) → (p3 ∧ ((False ∧ (True ∨ (p1 ∨ True))) ∨ p5)))) ∧ (True → p3)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753406905720658723026154887099 : (((False ∧ (((((p1 → (False → (False ∧ (p1 → False)))) ∨ True) ∧ (p3 ∧ (((p4 ∧ p3) ∧ p5) ∧ False))) ∨ False) ∨ ((False ∨ p3) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46152617243218295667309764760 : ((((((p1 ∨ (p5 → p3)) ∨ ((((p4 ∨ True) ∧ p1) ∧ (p2 ∧ ((p3 ∧ True) ∧ p1))) ∨ True)) ∨ (p1 ∧ p5)) → p4) ∧ (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173078942982442371607950616850 : ((p1 ∨ (((((p4 ∧ p2) ∨ p4) → False) ∧ (((p1 ∧ p1) ∧ p3) ∧ p5)) ∨ True)) ∨ (p1 ∧ (((False ∧ (p4 ∨ True)) ∧ p5) ∧ (True ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351807492865000946848844682334 : (p4 → (((((p5 ∧ ((False ∨ False) → p5)) ∧ p2) ∨ (p5 ∨ False)) ∧ False) ∨ ((((p3 ∧ (False ∨ (True ∧ (True ∧ p2)))) ∨ p3) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_47402329036153476968153578119 : (((True ∧ ((p4 ∧ p4) ∨ (((p5 ∨ (p2 ∧ ((((p4 ∧ p2) ∧ p5) ∧ (True ∨ p3)) ∧ (p4 ∧ p1)))) ∨ p4) ∨ p3))) ∨ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39600592344907479008839142035 : (((p2 ∨ ((p1 ∨ ((p2 ∨ ((((p3 → (p1 → False)) → p3) ∧ p5) ∨ p1)) ∧ (((p5 ∧ True) ∨ p4) ∨ True))) ∧ (p5 ∧ True))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719939236517506221379690925251 : ((((p5 → (p5 ∧ (False ∧ p4))) ∨ (p3 ∧ (p1 ∨ (p1 → ((True → ((p5 → ((p1 ∧ (p4 ∨ p3)) ∨ (p2 ∧ p2))) ∧ p4)) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138353693149768703315191125643 : ((p4 → (((p5 → (p4 → p4)) → ((p5 ∧ p1) ∧ (((True ∧ (False ∧ (p1 ∨ (p3 ∨ False)))) ∨ p2) → p2))) → False)) ∨ ((False ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147462061567704555444710389313 : (((True ∧ (((True → ((p5 → p5) → ((True ∨ ((p4 ∨ True) ∨ p3)) → (p4 ∧ p2)))) → p3) ∨ p2)) ∨ True) ∨ ((p3 ∨ p1) ∧ (p3 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715345535239537561492234837365 : ((((p5 → (((p3 → False) ∧ p1) ∧ True)) → (False ∧ (((True → p2) ∨ p2) → (((p4 → (p1 ∨ p1)) ∨ p5) ∨ ((p3 ∨ p5) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245975115265560495438666334682 : ((p4 ∧ True) ∨ ((p1 ∨ ((False ∨ (p5 ∧ (p5 ∨ True))) ∨ p3)) ∨ (p5 → (p5 ∧ (((p1 ∧ p3) ∧ (p3 ∨ p3)) ∨ ((p4 ∨ p4) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261620147836798154806609370562 : ((p5 → p5) → (((p2 ∧ True) ∧ (p5 ∧ ((((((p1 ∧ p3) → (p5 ∧ p4)) ∨ p3) → p5) ∨ False) ∧ (((p4 ∨ p5) ∨ False) ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684291829164352675307628154330 : ((((((p1 ∨ False) ∨ ((((p5 ∧ (p1 ∨ p4)) ∨ p5) → False) → p3)) ∨ ((p5 → p1) ∧ p2)) ∨ (p4 ∨ (False ∨ (False → (p3 ∨ p3))))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657956176774686339469106022500 : ((((p1 ∧ (p2 → (False ∨ ((p1 ∧ (((p5 ∨ p5) → (((((p2 ∨ p5) ∧ False) ∧ p2) → p3) ∨ False)) ∨ p3)) ∧ p1)))) ∨ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122135627659436651134613192251 : ((((((p1 → p4) ∧ (p5 ∧ (p1 ∧ (p3 ∨ p4)))) ∨ (p5 ∧ (((p5 ∧ (False ∧ True)) ∨ p1) → False))) ∨ p1) ∧ (p4 → p1)) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
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
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190176870896209301349984948394 : (((p4 ∧ (((p1 → p1) → False) → (False ∨ p4))) ∧ False) ∨ (((True → ((p5 ∧ p2) ∨ ((False ∨ p4) ∧ True))) ∧ p4) ∨ ((p2 ∧ p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_166654757176189308314964007752 : ((p1 → ((p1 → p3) ∨ (p2 ∨ (p5 ∨ (p2 → (p2 → (((p5 → p5) → False) ∧ p3))))))) ∨ ((((p4 ∧ True) → p2) → (p5 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309296345151380262473878880758 : (p2 ∨ ((((p5 ∧ ((p4 → (p2 ∨ True)) → ((((p4 ∧ True) ∧ p5) → (False ∨ p1)) ∧ ((False → p2) ∧ p1)))) ∧ p5) ∧ True) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56493873109439165518025895913 : (((p1 ∧ ((True → p3) ∧ p3)) → (((((p1 ∧ (p1 ∨ (p1 → p4))) → (p3 ∨ (((True ∨ p3) ∧ False) → p2))) → p4) ∨ p2) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266234881359147209013370756904 : (True ∧ (p5 → (((p3 ∧ (p3 ∧ (p5 ∧ ((p5 ∧ False) ∧ (p4 → ((((p4 → p4) ∧ p4) ∧ (True → False)) ∧ (p2 ∨ p2))))))) ∨ p5) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248832817347542989522999726668 : ((p3 ∨ p4) ∨ (((p2 ∧ (p4 → True)) ∧ p3) → ((((((p2 ∧ (p2 ∨ p4)) ∧ False) → p4) → p4) ∨ True) ∨ ((p1 ∧ p2) ∧ (p3 ∨ True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316431905225715875582148809992 : (p3 ∨ (p1 ∨ (((((p4 ∨ (p2 ∧ (p1 ∧ (p4 ∨ p5)))) → ((p4 ∨ (p3 ∨ p2)) ∧ ((p1 ∨ p2) → p2))) ∨ (True → True)) → p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ (p2 ∧ (p1 ∧ (p4 ∨ p5)))) → ((p4 ∨ (p3 ∨ p2)) ∧ ((p1 ∨ p2) → p2))) ∨ (True → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647516086722993724929019199733 : ((((p5 → (((True ∨ (False ∧ p4)) ∨ ((p1 ∧ (p2 → (False ∨ p3))) ∧ ((False ∧ (p5 → (p1 ∨ (False ∨ p2)))) → p4))) ∧ p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41984444641315325776583460827 : ((((p4 ∨ False) ∧ (p2 ∨ ((((((False → False) ∧ p1) ∧ p1) → False) ∨ ((p2 ∨ (p3 ∧ p5)) ∨ p4)) ∧ ((p5 → p1) → p1)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53767746759885411092849274271 : (((((p1 ∧ ((p3 ∨ p5) ∧ (p5 → p5))) ∧ p5) ∨ p3) ∨ (((p2 ∨ True) → False) ∨ ((True ∧ (True ∨ (p3 ∧ p3))) ∨ (True → False)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168847144574663688693227264675 : ((p3 ∨ ((False → p3) ∨ ((p4 ∧ p5) ∨ ((True ∨ (p1 → p3)) ∨ ((p4 → p5) → p4))))) → (p2 ∨ (((p4 → p4) ∨ (True ∨ p4)) ∨ False))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
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
          case inr h12 =>
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
        case inr h13 =>
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
theorem thm_5_vars_58409179733300115452762669143 : (((p2 ∨ p1) ∧ (True ∧ (p4 → (((((False → (p3 → p2)) → (p1 ∧ False)) ∧ False) → (((p1 ∨ (p4 → p3)) ∧ p1) ∧ p3)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46793069624793571400723937360 : (((p5 → ((p2 ∧ (p1 → (((p4 ∧ p3) ∨ p5) → ((p5 → p4) ∧ ((False ∧ p3) → p4))))) ∨ ((p1 ∧ p4) ∨ p1))) ∧ (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627390665576360887184009895575 : (((((((p3 → ((((p2 ∨ (p1 ∧ p2)) ∧ p3) ∧ (False ∨ p1)) ∨ p2)) → ((((p3 ∧ False) ∨ True) → p4) → p4)) → False) ∧ p2) → False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → ((((p2 ∨ (p1 ∧ p2)) ∧ p3) ∧ (False ∨ p1)) ∨ p2)) → ((((p3 ∧ False) ∨ True) → p4) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157891247734461441526940378586 : (((p4 ∨ ((((p3 → p2) ∧ False) ∨ (p3 ∨ p4)) → p3)) ∨ (((p5 ∧ True) ∨ False) ∨ (p4 ∨ True))) ∨ ((((p1 ∧ p1) ∨ p4) ∧ p4) ∧ p2)) := by
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
theorem thm_5_vars_336420095467078348237334140346 : (p1 → ((False ∨ ((p1 ∧ ((p4 ∧ ((False ∧ p5) ∨ p2)) → (((p3 ∧ p2) → p3) → p5))) → (p2 → ((p5 → (p1 ∧ p4)) ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208163090286425661828196335604 : (((False ∧ (p5 → p3)) → (True ∧ p1)) → ((((p2 ∨ ((p2 ∨ True) ∨ p2)) ∨ True) ∨ p2) ∧ (True → (p5 → (((p1 ∧ p3) ∨ True) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623669289360578573477839675173 : ((((p1 ∨ (((p1 ∨ (((p5 ∨ False) → (p1 → False)) ∨ (p3 → (((True ∨ p4) → (p2 ∨ False)) ∧ (p1 → True))))) ∨ p1) ∨ True)) ∨ p3) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57044977492811942977941129441 : (((p3 → (p5 ∧ p5)) ∧ ((((p3 → True) ∧ (True ∨ False)) ∨ True) ∧ (((p5 ∨ (p3 ∨ (False ∨ p3))) ∨ p5) → ((p4 ∧ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43074295506219094687401115844 : (((((p5 → ((p3 ∨ (((((p3 ∨ (True ∨ True)) ∧ False) ∨ (False → True)) ∧ p1) ∨ ((p2 ∨ p4) ∧ p4))) ∨ p3)) → p5) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110958661743613927622046315304 : (((((p4 ∧ (p1 ∧ (((False → (p4 ∧ True)) ∧ False) ∧ (p2 ∧ p1)))) ∨ (((False ∧ False) → p1) ∨ p4)) ∨ (p5 ∨ p4)) ∧ True) ∨ (True ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62666584162752620639791422661 : ((p4 ∧ (((p1 ∧ (True ∨ (p4 ∨ (p1 → True)))) ∨ (p5 → ((((p4 ∧ p3) ∨ (p3 ∧ p5)) ∨ (p4 → (True ∨ p2))) ∨ p4))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42844426045658975806599276235 : (((p2 → (((((((p3 ∧ ((p1 → (p5 → p2)) → ((p1 → p1) ∧ p2))) → p5) → True) ∨ (p5 ∧ p3)) → p4) → p3) ∨ False)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114013398540718946792749950397 : ((((((((p1 ∨ (p3 ∧ p3)) → ((p4 ∧ (False ∨ (True ∨ True))) → p3)) ∨ p5) ∨ p1) ∧ True) ∨ p2) ∨ ((True ∨ p2) ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67435768099706867350252113134 : ((p1 → (((((p4 ∨ (p4 ∧ ((p1 ∨ False) → p4))) ∧ p5) → False) ∨ (p2 → (((p3 ∧ p1) ∨ p1) ∧ p5))) ∧ (p2 ∧ (p4 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611299478029495107475399584430 : ((((((p1 → p2) ∨ ((p1 → (p5 → (((False ∧ (False ∧ p2)) → (True → False)) → (False ∨ ((p5 → p4) ∧ p3))))) ∨ p2)) → p4) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190207042618228545771824031734 : (((p5 ∨ (p3 ∨ (True ∧ (False ∧ (p3 ∨ False))))) ∧ p2) ∨ ((((False → ((False ∧ (p3 ∧ (p1 ∨ p1))) ∧ p5)) ∨ (False ∧ p2)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165067869952943842593860108030 : (((p2 ∧ (p1 → (((p3 → (((p3 → True) ∨ True) → p5)) → (p3 ∨ True)) ∧ False))) → False) ∨ (((p2 ∧ ((p1 ∧ p2) ∧ p4)) ∧ p5) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201353181771751478704526995914 : ((p5 → (p4 → ((p1 → (p4 ∧ False)) ∧ p2))) → ((p2 → p3) → (((p4 ∧ (p5 → p5)) ∨ ((((True ∧ p4) ∧ p4) → p2) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185241611683668247588515061553 : ((False ∧ (p4 ∨ ((p5 → (p5 ∨ (p5 ∨ (False ∨ False)))) → p1))) ∨ ((p2 ∧ (p3 ∧ (p2 ∧ p1))) ∨ ((False ∧ ((p5 → False) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354290341613711877489561761615 : (p5 → (((((False ∧ p4) ∨ ((p3 ∧ ((p5 → p3) ∨ (p1 → (True ∧ ((p4 ∧ p2) ∨ p1))))) ∨ p1)) ∧ False) ∨ (p1 ∨ (True ∨ p5))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299389822418508522285123903609 : (False ∨ ((True ∧ ((p1 ∧ ((False → (p2 → p4)) → ((p2 → ((p5 ∧ (True ∨ p2)) ∨ True)) ∧ (False ∧ (p1 → True))))) ∧ (p3 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746438785126656495332107763604 : ((((p2 ∨ p2) → ((p2 → False) → (p5 ∨ ((((p2 → ((True ∨ True) → p1)) ∨ (p3 → True)) → ((False ∧ (p5 ∨ p1)) ∨ False)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60304263512027045571571065779 : (((p1 → p2) → (p1 ∧ ((((p4 ∨ p5) → (False → (p4 ∧ (((True ∧ True) ∧ ((p5 ∨ True) ∧ p3)) → (False → False))))) → p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41152929666270904197654939959 : (((((True → p5) ∨ (p3 → (((p1 → (p4 → (True ∧ p4))) → p5) ∨ (((p5 ∨ p2) ∨ p2) ∨ p3)))) ∨ (p3 ∧ (p4 → p2))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776509304587798717020692168233 : (((p1 ∨ ((((((True ∧ p3) → p1) → ((True → p1) ∧ p5)) ∧ (p2 → p1)) ∧ (p1 → (False → ((p5 ∨ p3) ∨ (True → True))))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_322398657403421026281035296228 : (p5 ∨ ((((True ∧ p2) ∧ ((p4 → p5) → ((True ∧ (p2 ∧ True)) ∨ (p5 ∨ p2)))) → ((True → ((False ∨ p5) → p4)) ∨ (p3 → p3))) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201093222442210463805819745813 : ((True → (((p5 ∨ (True ∧ p5)) ∧ p3) ∧ p2)) → ((((((p4 ∧ p2) ∧ p1) ∨ p3) → p5) → p5) ∧ ((p3 → ((p4 ∧ p1) ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115559597614495748156872753858 : ((((((p5 → p3) ∨ True) ∨ p5) ∨ p5) ∧ ((((True ∨ (((True ∨ False) → p3) ∧ (p2 ∧ (p5 ∨ p3)))) → p5) ∧ p1) ∨ True)) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41761079832853020061461521100 : (((((p1 ∧ p4) ∨ (p4 ∧ p4)) ∨ (((p1 ∧ ((p2 → (p4 ∨ False)) ∨ False)) ∧ (p2 ∧ p5)) → (False ∨ (p2 ∧ (p3 ∨ p1))))) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_474036673949600242938121696717 : ((((True → ((p4 ∨ False) ∨ (True ∧ (p2 ∧ (False → (p2 ∧ True)))))) → ((False ∨ (True ∧ (p1 ∧ (p4 → False)))) ∨ ((p4 → p4) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49464615900026937006021962015 : ((((p3 → ((p1 ∨ p3) → (p1 ∨ (p4 → ((((p5 ∨ p3) ∨ p3) → (True ∨ p2)) → (True ∨ p4)))))) ∨ p3) → ((True → p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164477003278553386846252975672 : (((((p4 → p1) ∧ (((True → ((p2 ∨ p5) ∧ p2)) → (p3 ∨ p1)) ∧ p3)) ∨ p3) ∧ p5) ∨ ((p4 ∧ p3) → ((p3 ∨ p2) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52612284358299285842114569047 : ((((((False → p3) ∨ p5) → True) → ((p4 ∨ (p1 ∧ p5)) → (p5 ∨ p2))) ∨ (p2 ∨ ((p1 → p4) ∧ ((p4 → p4) ∧ (p4 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135732287810180405347174897753 : (((((((p5 ∨ p2) ∨ p3) → (((p3 ∨ p4) ∧ False) ∧ p1)) → p5) → False) ∨ (p1 → (((p1 ∨ p3) ∧ p5) → p1))) ∨ ((False ∧ p4) ∨ p5)) := by
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
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55599801760909420124570200067 : (((True → ((p4 → (p3 → p3)) ∧ False)) → ((((((p4 → (p1 ∨ True)) ∨ p2) ∧ ((p4 ∨ p2) → False)) ∨ p4) ∨ False) ∧ (False ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148790845622298944124534558446 : (((p3 ∨ (p2 ∨ (p1 ∧ (p5 ∧ p2)))) ∨ (True ∨ ((((True ∧ p5) → (p4 ∨ (p1 ∧ p1))) → p2) → p4))) ∨ ((False ∧ p3) ∨ (p3 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116064027684973088815624386822 : ((((True ∨ False) ∧ p3) ∧ (((((p5 → (True ∨ (p3 ∨ (True ∧ p3)))) → p5) ∨ p4) ∧ p4) → ((p3 ∧ p2) ∧ (p3 → False)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



