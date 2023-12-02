variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174091707333359069280402613643 : (((((True → (True ∧ (False ∧ p1))) ∧ p4) ∨ ((p1 ∧ p2) ∧ p3)) ∧ (False → True)) → (((True → (p4 → p2)) ∧ (p4 ∨ True)) ∧ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159057599252746789604816488269 : ((p5 ∨ (((p4 → (p1 → (p5 → (p4 ∧ p1)))) → p1) ∨ (p5 ∨ (True ∧ ((True ∨ p1) ∨ p5))))) ∨ ((p4 → False) → ((p3 ∧ p3) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40479288260306317237479274440 : (((((False → p5) ∧ (((False ∨ (((((p5 ∧ p1) → (p1 → (p3 → p3))) ∧ True) ∧ (p5 ∨ p3)) → p3)) → True) → p4)) ∨ p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165096431249178914498416796673 : (((p4 ∨ (True → (((((p3 → p1) ∨ (p2 ∧ p2)) → p3) ∨ False) ∧ (True → p2)))) → False) ∨ ((False ∨ p2) ∨ (True ∧ ((p3 ∨ True) → True)))) := by
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
theorem thm_5_vars_59243606169981383231548432593 : (((p2 ∨ p3) ∨ ((((((p2 ∧ p3) ∨ True) ∨ ((p2 ∧ False) → (p4 → (True ∨ (p5 ∧ (p2 → p3)))))) ∨ True) → (p4 → p1)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184358548077726367018058704088 : (((False ∨ ((p2 → False) ∨ ((False ∨ p3) ∨ (False → True)))) → False) ∨ (p1 ∨ ((True ∧ (p1 ∨ (True ∨ ((p5 → True) → (p3 ∨ p4))))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116782605866625872784995317720 : (((p1 ∨ False) ∨ (p5 ∨ ((p3 ∨ p3) → ((((p1 → p5) ∨ p3) ∧ (False → ((p4 → (False ∧ False)) → (p3 → False)))) ∨ p2)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44673341988782837808890776693 : ((((((p1 ∨ p5) → (p2 ∧ p4)) → p1) → (((True → (False → ((((p1 → p2) ∧ (p1 → False)) → p3) ∨ False))) ∨ False) → p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793289576374056212558241029560 : (((True → (p2 ∧ (p4 → (((((p3 ∧ (False ∨ p5)) ∧ (((p3 ∧ (p4 ∧ ((p3 ∨ p5) ∨ p1))) ∨ p2) ∧ p3)) ∧ p3) ∨ p3) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45272841393278915760115082493 : (((p2 ∧ ((((((False ∧ False) → (((False → False) → (p5 ∧ p3)) → p2)) ∧ (p2 ∨ True)) ∧ ((True → p2) → p1)) → p3) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597603146350702247901504440543 : ((((((p4 → (p1 ∨ p4)) ∧ p3) → ((((((p1 ∧ (True ∧ False)) → p4) → False) → ((p3 → (p1 ∨ p1)) → p1)) → False) ∧ p4)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104513098365751389926920536599 : (((((((True → p1) ∧ (p2 ∨ p5)) ∧ p5) ∨ ((p4 ∨ (p4 ∨ (p5 ∧ p2))) ∧ (True ∨ (p4 → p3)))) ∨ True) ∨ (False → p3)) ∧ (p1 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56657000703426522601955580163 : ((((p4 ∨ p1) ∧ p3) ∧ (p3 ∧ (((((p5 ∧ p4) ∧ (p5 → (p3 → False))) → ((((p4 ∧ p4) → False) ∧ True) → p5)) ∨ p5) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238201431472224231259292341387 : ((True ∨ p4) ∧ (((p1 ∧ (False ∨ (p2 ∨ (True ∨ p2)))) ∨ p3) ∨ (p3 ∨ (p4 → ((p1 → ((p3 → False) ∧ True)) → (False → (p3 → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57395258156318196310599759944 : (((False ∨ (p1 ∧ p1)) ∨ ((p2 → (((True → p1) → p5) ∧ ((p3 → p3) → p1))) → ((((p5 ∨ p2) ∨ (p2 → p2)) ∨ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52594195593913540588996541602 : ((((((False ∨ (p5 → p1)) ∨ p2) ∧ p1) ∧ (p4 ∧ (p5 ∧ (False → True)))) ∨ (((p2 → (False ∨ p2)) → (True → p1)) ∧ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114151662338308807042303072171 : ((((((False ∧ p3) ∧ False) → (False → ((((p1 ∧ (p3 → p1)) ∨ (p5 ∨ p2)) → False) ∨ p5))) ∨ True) → ((p2 ∨ p3) ∧ p2)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622610598402086273243942623575 : ((((p4 ∧ ((p2 ∨ (True ∨ ((((p2 ∨ ((p2 ∧ True) → p4)) ∨ p5) ∧ p2) ∧ (p5 → (p3 → (p3 ∨ (p5 ∧ p4))))))) → False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707270962616223667735444245945 : (((((False ∧ (p4 ∨ (p5 ∨ p2))) ∧ (p4 ∧ p4)) ∨ (((p3 → False) → ((True ∧ (p5 ∨ p2)) → (p3 ∧ p3))) → (p5 → (p2 → True)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149848390710322144601696630177 : ((p1 ∨ (p3 ∧ (p3 ∨ ((p3 → ((p3 ∨ p5) → ((p3 → p4) → (p4 ∨ p4)))) ∧ ((p3 → p3) ∨ p4))))) ∨ (((p3 ∨ p3) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166438758921822862515875224747 : ((p2 ∨ ((((False → p4) ∧ ((((p4 ∨ p5) ∨ p5) ∧ True) → (p2 ∧ p3))) ∨ p2) ∧ True)) ∨ ((False ∧ (True ∧ p1)) → (p4 ∧ (p4 ∨ True)))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119089641536914149546019277201 : ((p1 → ((((p4 → p1) ∧ (((p1 ∧ p4) ∨ p2) ∧ (p5 → p3))) → p4) → (((True → True) → False) ∨ ((p4 ∨ True) ∧ True)))) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_326951542491716316308985715816 : (True → ((((False → ((p4 ∧ (p1 → (p4 ∨ False))) ∨ ((p3 → ((p2 ∧ p2) ∧ (p3 ∨ (False → False)))) ∨ p5))) → p1) ∨ (False ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117852422614090877491491865591 : ((p5 ∧ ((((((p5 ∨ p4) ∨ True) ∨ p3) → (True ∧ (((p2 ∧ (True ∧ (p3 ∨ (p2 ∨ False)))) → p5) → False))) ∧ p5) ∧ p2)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165242044945826250317944933638 : (((p5 ∧ ((p5 ∧ (p4 ∧ p5)) ∧ (((p3 ∨ p2) ∧ (False ∨ p5)) → p3))) ∨ (True ∨ p4)) ∨ (False → (p1 ∨ (p3 → (p2 ∨ (False ∨ p5)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197800287622464489665191799947 : ((((p3 ∧ p5) ∨ p2) ∨ ((True ∨ p4) ∧ p3)) ∨ (((p5 → p4) ∨ ((False → ((False → (True ∧ (p1 ∧ (p4 ∧ False)))) ∧ p4)) ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758388951237010290572432266412 : (((p2 ∧ (((p2 ∧ (p2 ∨ ((((p1 → False) ∧ p1) ∨ p4) ∨ p5))) ∨ (((p4 ∧ True) ∨ ((p4 ∨ (True ∨ p2)) ∧ True)) ∧ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679946466710151602529911252581 : (((((((p1 ∨ ((p5 ∧ ((p3 → p3) → True)) ∧ ((p2 ∨ p3) → True))) ∨ p4) → (p2 → True)) → p1) → ((p5 ∨ p1) ∨ (p5 ∧ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((p5 ∧ ((p3 → p3) → True)) ∧ ((p2 ∨ p3) → True))) ∨ p4) → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115654945955620955936316273221 : ((((p1 → (True ∧ False)) ∧ (p4 ∧ p2)) ∨ ((p4 ∧ (p3 ∧ (p3 ∧ (p5 → p3)))) ∨ ((False ∧ (p5 ∨ p4)) ∨ (p2 ∨ True)))) ∨ (p4 ∧ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662603236955461493174559638639 : (((((p3 → ((False → p2) → (p2 → True))) → (True → ((False ∨ (((p4 ∧ p1) ∨ p4) → ((True → False) ∨ True))) ∧ False))) → (p4 ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((False → p2) → (p2 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141811877511776937619737617569 : (((p4 ∧ p1) ∨ (((((p3 ∧ p3) ∧ p5) ∨ ((p5 ∨ p1) ∨ p4)) ∨ ((p1 → (p1 → (True ∧ p2))) → False)) ∨ p1)) → (False ∨ (False → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h18
              -- False on the left can always be used.
              apply False.elim h18
            case inr h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h20
              -- False on the left can always be used.
              apply False.elim h20
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h22
            -- False on the left can always be used.
            apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233993329676981020933724534377 : ((p5 ∨ (False ∨ p2)) → (p3 → (True → (True ∧ (((p3 ∧ ((((p3 ∨ p2) ∨ p2) ∧ p2) → (True → (True ∧ False)))) ∨ p2) ∨ (p5 → p3)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65203774590082789902120585997 : ((p3 ∨ ((((((True → (p4 ∧ p1)) ∨ p5) → (((p1 → p2) ∧ ((p3 → p2) ∨ (p1 ∧ (p1 ∨ p1)))) → p2)) → p5) → p2) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319368996946386319011203166281 : (p4 ∨ ((((((True ∧ p4) → p1) ∧ p4) ∨ (p5 ∧ p3)) → (p3 ∧ (p4 ∨ p2))) ∨ ((True ∨ ((p4 ∨ (p2 ∨ (p1 ∧ p3))) ∨ p2)) ∨ False))) := by
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
theorem thm_5_vars_48321398795542975397588188189 : (((p1 ∨ (((p5 ∨ False) ∧ (((False → (p2 → p5)) ∨ ((p1 ∨ (p1 → p4)) ∨ False)) ∧ ((p2 → p3) ∨ p1))) ∧ True)) → (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116702803338293017644718296797 : (((p1 ∧ True) ∨ ((((p1 → ((p5 → (p3 ∧ (p1 → p2))) ∨ p4)) → (p5 ∧ (p4 → (False → p5)))) ∧ (p5 ∨ p1)) → False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671438375235467439650920921611 : ((((p1 → (p2 → ((((p4 → (p3 ∧ (p2 ∨ p2))) → p4) → p1) → (((p2 → p3) ∨ True) ∧ (p5 ∨ p3))))) ∨ ((p4 → p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135456942447183134402015826798 : ((((((p1 → p4) → ((p3 ∧ ((False ∧ False) ∨ (p2 ∨ p5))) → (True ∨ p4))) → p1) → p5) → ((False ∨ p3) ∨ p2)) ∨ (True ∨ (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165026509194601642797961287908 : ((((False → (True ∧ p3)) ∧ ((p4 ∨ p4) ∨ (p5 ∧ (p1 ∨ (p1 ∧ (p4 ∧ p2)))))) → p3) ∨ (False → (((p1 ∧ p5) ∧ (p1 ∧ False)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798041467851457665332429323447 : (((p1 → (((((p1 ∨ ((p4 ∧ (False ∧ False)) ∨ (p3 → p1))) ∨ (p2 → ((p1 ∧ p5) → p1))) ∧ p3) ∨ p4) ∨ ((p4 → p3) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311205365042038032472095920821 : (p2 ∨ ((p5 ∨ True) → ((p2 ∨ True) ∧ (True → (((False ∧ ((p5 ∨ True) → (p4 → p2))) ∧ (p1 ∧ p5)) ∨ ((p3 → p3) ∧ (False → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134504084621755481415297535844 : (((((p3 ∧ (p4 ∧ (p2 ∧ False))) ∨ (((False ∨ p3) ∧ (p5 ∨ p1)) ∨ ((p2 ∨ False) → (True ∧ p5)))) ∨ False) → p2) ∨ ((p3 ∧ False) → p4)) := by
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
theorem thm_5_vars_67987131527141280866479133962 : ((p2 → ((p4 ∨ True) ∧ (True ∧ ((((False → p3) ∨ False) ∧ ((((p5 ∨ (p1 ∧ False)) ∨ p5) → (p4 ∧ p3)) → (p5 ∧ p5))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301517288737089867096149156452 : (False ∨ (((True ∧ True) ∧ p5) ∨ (((True ∨ (False ∨ p2)) → False) → (((p4 → p5) → (((p4 ∨ False) ∧ p3) ∨ False)) ∨ (p4 → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (False ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258758368202692391973795802972 : ((True → False) → ((((p1 → (p2 ∧ ((p1 ∨ (((p4 ∨ False) ∨ (p5 → (p5 → (False ∨ p1)))) ∧ p2)) ∨ p4))) → p4) ∨ (p1 ∧ True)) ∧ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193858570685898961079247373541 : ((True ∨ (p1 ∧ (((True ∧ (p2 ∨ p2)) ∧ p3) → p2))) → (p2 → (p1 → (((True → ((p4 → (p2 ∨ (p2 → p1))) → False)) ∧ p4) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342675934166859471757323948266 : (p2 → ((True → ((p5 ∧ p4) ∨ (p1 → ((False ∨ p3) ∧ False)))) ∨ ((((p5 → (p5 ∧ p3)) ∨ True) ∧ ((p2 ∧ p4) ∧ p4)) → (p1 → True)))) := by
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
theorem thm_5_vars_168324074676649729390779966396 : (((p2 → p3) ∧ (((p1 → True) → False) ∧ (p1 ∨ (p2 ∧ (p5 → (p5 ∧ (p1 ∨ False))))))) → (((p5 ∨ ((True → True) ∨ False)) → p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h13
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585364215258497651426236693746 : ((((((((p3 ∧ p2) ∨ (((False → p4) ∧ False) → (((p5 ∨ p1) ∨ True) ∧ False))) → (((p2 → p5) ∧ p2) → p1)) ∧ p1) ∧ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806074486757537322646734892409 : (((p4 → ((p2 ∧ ((True ∧ p1) ∧ (p1 → ((p1 → ((((p4 ∨ p5) → p4) ∨ (p5 ∨ (True → (p2 ∨ False)))) → p2)) ∨ False)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259573010519812955811604813231 : ((p1 → True) → (((((p2 ∨ False) ∨ p1) ∨ (p1 ∨ (p5 ∨ True))) ∨ (((p1 ∨ p3) ∨ p3) ∨ False)) ∨ (((p4 ∨ False) → (p1 ∨ p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_47261521592173734692228885014 : (((((True ∨ p5) ∧ (False ∨ (p5 → p5))) → (False ∧ ((((p4 ∨ (False → (p1 ∨ p4))) ∧ (p5 ∨ p5)) ∨ True) ∨ p3))) ∨ (p3 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791295704314743101435153593548 : (((True → ((((p2 ∨ (((p2 ∨ p5) → ((p5 ∧ True) ∧ (p2 ∧ p2))) ∧ ((True → p2) → p1))) → ((p2 → p4) ∧ p4)) ∨ True) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761529886583906108991791390068 : (((p3 ∧ ((((True → ((p4 ∧ p3) → (((p2 → (p3 ∨ p4)) ∨ p5) → (p2 ∧ (p4 ∨ ((p5 ∧ True) ∧ True)))))) ∧ p5) ∨ p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184276390140133476362817540677 : ((((p1 → (((p2 ∨ p2) ∧ p2) ∧ True)) → (p2 → p5)) → False) ∨ (False → (((p3 → (True → (p1 ∨ False))) ∨ p4) ∨ ((p5 → p4) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116642847877151476351333552011 : (((p2 → p3) ∧ (((p2 → (((p2 ∨ (True ∧ p3)) → p3) → (p4 ∧ (p5 ∧ True)))) → ((p5 ∧ True) → (p4 ∨ p3))) ∨ p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323804023741891439438031103194 : (p5 ∨ ((False ∧ ((p4 → (p1 ∨ (((p2 ∧ (p1 → p5)) ∧ p2) ∧ p4))) ∧ ((p1 ∨ p2) ∧ p2))) ∨ ((False → ((p3 ∧ True) ∨ p5)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147649387848296729358123384241 : ((((((((p5 ∨ ((p2 → p2) → p4)) → (False → (True ∧ True))) → p1) ∨ p5) ∨ p1) ∧ (p3 ∧ p5)) → p2) ∨ ((False ∧ p2) → (p5 ∧ p2))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46374598247174711671511061694 : (((((True ∨ p4) → (True → ((p1 → False) → ((p5 → p5) ∨ p1)))) → ((p4 ∧ (True ∨ (p2 ∧ (p2 → p4)))) ∧ p5)) ∧ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125532413030898014248858131055 : (((True → False) ∧ ((((p5 → ((p3 ∨ p1) → False)) ∧ ((p3 → p4) → ((p2 ∧ p2) ∨ (p4 ∨ (p3 ∨ p2))))) ∧ p2) → p2)) → (True ∧ p2)) := by
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
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191908411102448974118429530091 : ((p5 ∨ ((p2 → p4) ∨ (p5 ∧ ((p1 ∨ p2) ∧ False)))) ∨ ((True ∨ ((p3 ∧ ((False → p4) → p5)) → ((p5 ∧ False) ∧ False))) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654066464480527270715373429718 : (((((p1 → (((((((p5 ∨ (p3 ∧ True)) ∧ p1) ∨ p1) → True) ∧ ((False → p5) → (p3 ∨ False))) ∨ True) ∨ p3)) ∧ True) ∨ (p4 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200515968123768465924299820843 : (((False ∨ p5) → (p4 ∨ ((False → p3) ∨ p4))) → (((p1 ∧ (False ∧ p5)) ∧ (True ∨ (p1 ∨ True))) ∨ ((p1 ∨ (p5 ∨ (True ∧ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593037903052753712380662892637 : (((((((False → (((True ∨ ((p3 ∨ p1) ∨ False)) ∨ (p5 ∧ p4)) ∧ p1)) → ((True → p2) → False)) ∨ p1) ∨ ((p4 → p4) ∨ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709016718446010113169399110840 : ((((((True → p5) ∧ p1) ∧ ((p2 ∨ p2) → p3)) → ((p4 ∧ (False → (False → (p1 ∨ p1)))) ∧ (((True ∧ p2) ∧ (p3 ∨ p5)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797120090577511742254702864081 : (((p1 → (((p1 ∧ False) ∨ ((p3 ∨ (((p2 ∧ True) ∨ (True ∨ p5)) → (p1 ∧ False))) ∨ (False ∧ (True ∨ ((p5 ∨ False) → p1))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41804418475837859126341729924 : ((((True → ((False ∧ True) ∧ False)) → (((p3 ∨ ((p2 ∨ p1) ∨ p2)) ∨ False) ∨ (p5 → ((True → (p4 ∧ p4)) ∨ (p2 ∨ p3))))) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50622518839977421220705842034 : (((((False ∨ (p5 → ((False ∧ True) ∧ ((p2 ∧ p4) ∨ (False → False))))) ∨ p2) ∨ (p4 → (False ∨ p2))) → ((p1 ∨ (p3 → p4)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198240830333233987508603037835 : ((True ∧ (p2 ∧ ((p5 ∨ (p1 ∨ p3)) ∨ p1))) ∨ ((p5 → (((p3 ∧ ((p3 → True) ∨ False)) → (p2 → False)) ∧ True)) ∨ ((True ∧ False) → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174272586057976058909619532217 : (((((p4 → True) ∨ (p2 → p5)) → (p4 ∧ (p3 ∧ p2))) ∧ ((p3 ∨ False) ∧ p3)) → ((((True ∧ p2) ∨ ((p5 → p4) → p2)) ∨ True) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316752741420485303967925378529 : (p3 ∨ (True → (((((p3 → ((p1 ∨ p4) ∧ True)) ∧ p5) ∧ True) ∨ (False ∧ p4)) ∨ (False → ((p4 ∨ p2) ∨ (((True ∧ True) ∧ p3) ∧ True)))))) := by
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
theorem thm_5_vars_256892384598075873586683460306 : ((p1 ∨ p4) → ((p3 → (p4 → (((((((((p5 ∨ p5) ∧ p2) → False) ∨ p4) ∨ p5) → p2) ∨ p4) ∧ p3) ∧ (p3 → p3)))) ∧ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147173561219258874679936188286 : (((False ∨ (p4 ∧ ((((True ∨ p4) → p3) ∧ p5) ∧ ((p1 ∨ (p4 ∨ ((p3 ∨ p1) ∧ p4))) → p1)))) ∧ p4) ∨ ((False ∧ False) → (p4 ∧ p3))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65100408107127871226776064268 : ((p2 ∨ (p3 ∨ ((p4 ∨ ((False ∧ ((p4 ∨ (True → True)) → (True ∨ p1))) ∨ ((p1 → ((True ∨ False) ∧ p5)) → (p4 → p5)))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41872928019255028691036644065 : (((((p2 → p5) → p4) ∨ ((p4 ∧ p2) ∨ (p3 ∧ ((((False ∧ (p5 ∧ (p1 → ((True → False) → True)))) ∨ p1) ∧ True) ∧ p4)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783076074050735049036938258507 : (((p3 ∨ (((p3 ∨ (((False ∧ True) → (True ∨ (p4 ∧ p1))) ∨ p3)) → ((p3 ∧ p1) ∧ (((True → p4) → True) → p4))) → (p1 ∨ p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (((False ∧ True) → (True ∨ (p4 ∧ p1))) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733984456755666993357970193117 : ((((True ∨ p1) ∧ ((((p4 ∨ ((False ∨ p5) ∨ ((((p2 ∧ p4) ∧ p5) ∧ ((p3 ∨ False) ∧ True)) ∨ p5))) ∧ p5) ∨ True) ∨ (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337672436903030486855038840650 : (p1 → (((p5 → p5) → (((((p2 ∨ (p5 → False)) ∧ False) ∧ (True ∧ (True ∧ p4))) ∧ p3) ∧ p4)) ∨ (p5 ∨ (p3 → (p2 → (p3 ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116119455357913055987679843627 : ((((p3 → p3) → p1) ∧ ((p5 ∨ ((p2 → (False ∧ False)) ∧ ((p4 ∨ p2) ∨ ((p1 ∧ (p5 ∨ False)) ∨ p3)))) → (p2 → p5))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114037334333759430638141286243 : ((((p1 → ((p5 ∧ (((p4 ∨ False) ∨ ((p3 → p5) → (p3 ∧ p4))) ∨ (p2 ∨ p1))) ∧ True)) → p4) ∨ ((False ∨ False) → p1)) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53857881640181999089847885248 : ((((False ∨ (p5 → p4)) ∨ (False ∧ (p2 ∧ (p1 ∨ p5)))) ∨ (((p1 ∧ (True → (p5 → p1))) ∨ p5) → ((p3 ∧ False) → (True → p5)))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199327728774685045581235432201 : (((((p5 → (p4 → p5)) ∧ True) → False) ∨ p1) → (((False ∧ p4) ∨ (p4 ∧ ((((p4 ∨ (False → p2)) ∨ True) ∨ (False → p1)) ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_2813986803771485789642819357 : (((p5 ∧ (p2 ∨ p3)) ∧ p3) → (True → (((p4 ∧ False) ∧ p1) ∨ (((True → (p4 ∧ (((p3 → p4) ∨ p3) ∨ True))) ∨ p3) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148421106830896610253346762518 : ((((p1 ∧ (p2 ∧ (((True → p4) → p5) ∨ True))) ∨ ((p5 ∨ False) ∨ p3)) → (p1 ∧ (False ∨ (True ∧ p4)))) ∨ (((False → p4) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165347077148553906985781051911 : ((((p1 ∨ False) ∧ (((((p3 ∨ p4) ∨ p5) → True) → p2) ∨ p5)) ∧ (p4 ∨ (p2 → p5))) ∨ (((p3 ∧ (False → True)) ∧ p2) → (p2 ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650917628282040290974891107320 : (((((False ∨ ((p5 ∧ (p2 ∨ p4)) ∧ p3)) ∧ ((p1 ∨ False) ∨ ((((p3 → p3) ∧ p5) → (p4 ∧ p2)) ∧ (p4 ∨ p5)))) ∧ (p3 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78915729027004131341385658658 : ((((True ∨ p3) → (((((p3 → ((True ∧ p2) ∧ False)) ∧ ((p4 → (False ∨ p4)) ∧ p3)) ∨ False) ∧ (False → p2)) ∧ p1)) ∧ (p1 ∨ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606409917638335506534009747114 : (((((((True ∧ p1) ∧ (((False → ((p1 → p3) ∨ ((True ∨ p3) ∨ p2))) ∧ p3) ∧ (p1 ∧ ((p2 ∧ p4) → p1)))) ∨ p4) ∧ False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134195564927665700094682180736 : ((((p4 ∨ (False ∧ ((p4 ∨ (False → p2)) ∧ (p3 ∧ p5)))) ∧ (((False → (True ∧ p1)) → True) ∧ (p4 ∧ p3))) ∨ p3) ∨ ((p2 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317703848613054464147800045504 : (p4 ∨ (((((((True ∨ (p5 ∧ (p1 ∨ False))) ∨ (p5 ∧ ((p3 → p5) ∧ p4))) ∧ False) ∨ (p4 ∧ (p3 ∨ p4))) ∨ p5) ∨ (True ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39234605620549410285964007167 : (((False ∧ ((((((p4 ∧ p4) ∧ (p5 ∧ p2)) → (False → (p2 ∧ p3))) → ((p3 ∨ ((p5 → p5) ∨ False)) → False)) ∧ p3) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174241419582899154505013424122 : (((True ∨ (p2 ∧ (False ∨ ((False ∧ ((p1 ∧ p5) → p1)) ∧ p4)))) → (False → False)) → (p2 ∨ (p5 ∨ ((p2 → (p1 ∧ (p5 → p4))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208402858905173917995163909818 : (((True ∨ p5) ∨ (True → (p5 → False))) → (((p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) → False) → (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h10 : ((p5 → (True → (p3 ∨ p5))) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h11
            -- Implications on the right can always be decomposed.
            intro h12
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h13 := h9 h10
          -- One of the premise coincides with the conclusion.
          exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h5
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h21 : ((p5 → (True → (p3 ∨ p5))) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h22
            -- Implications on the right can always be decomposed.
            intro h23
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h24 := h20 h21
          -- One of the premise coincides with the conclusion.
          exact h24
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h16
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h27 : (p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h33 := h26 h32
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- False on the left can always be used.
        apply False.elim h35
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h36 := h2 h27
    -- False on the left can always be used.
    apply False.elim h36
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h39 : (p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
          have h44 : ((p5 → (True → (p3 ∨ p5))) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h45
            -- Implications on the right can always be decomposed.
            intro h46
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h45
          -- We have shown the premise of h43, we can now drive its conclusion.
          let h47 := h43 h44
          -- One of the premise coincides with the conclusion.
          exact h47
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h48 := h2 h39
      -- False on the left can always be used.
      apply False.elim h48
    case inr h49 =>
      -- One of the premise coincides with the conclusion.
      exact h49
  case inr h50 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h51 : (p5 → ((False ∨ (((p5 → (True → (p3 ∨ p5))) ∨ p4) → p2)) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h52
      -- Implications on the right can always be decomposed.
      intro h53
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h54 =>
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h56 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h57 := h50 h56
        -- We want to use the implication h57 based on <expert-advice>. So we show its premise.
        have h58 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h52
        -- We have shown the premise of h57, we can now drive its conclusion.
        let h59 := h57 h58
        -- False on the left can always be used.
        apply False.elim h59
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h60 := h2 h51
    -- False on the left can always be used.
    apply False.elim h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150929369092866382349724984745 : ((((p4 ∨ True) → (((p5 → p2) ∧ ((p5 ∧ p4) → (p1 → (p3 ∨ (p4 ∨ (p2 ∨ p3)))))) ∨ p1)) ∨ True) → ((p5 → (True → p3)) ∨ True)) := by
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
theorem thm_5_vars_775662091929870855360786482872 : (((False ∨ (p1 ∨ (False ∧ ((False → p5) → ((((p4 ∨ ((p4 ∨ p3) ∧ (((p3 ∨ p4) → p4) ∧ True))) ∧ p1) ∨ p5) ∧ (p3 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350085776150946108551179016395 : (p4 → (((p5 → (p2 → ((p3 → (False ∧ ((p5 ∨ False) → ((True ∨ (p5 → (True ∧ p5))) → True)))) → (p3 → p4)))) → (True ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69234520077784835756924718886 : ((p5 → (((p4 ∧ (False ∧ p4)) → p1) → ((((p3 → p4) → p2) ∧ ((True ∧ (True → True)) → (p4 ∧ p5))) ∨ (p1 → (True ∨ False))))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321162836447805510153740488327 : (p4 ∨ (p2 ∨ (p4 → ((False ∧ (p2 ∨ p4)) ∨ ((False ∧ ((p5 ∧ ((p1 → True) ∨ True)) → (False ∨ p1))) ∨ ((p1 ∧ False) → (p5 ∧ p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60853175022599612136476960247 : ((True ∧ (p3 ∨ (p2 ∧ ((p4 ∨ ((p4 → (p2 ∧ (True → p5))) ∨ (True ∨ p3))) ∧ ((p2 ∧ ((False → True) → False)) ∧ (p4 → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39593766144134004302987124092 : (((p2 ∨ ((((p1 ∧ (((((p4 ∨ p3) → True) ∧ (p2 ∨ p1)) → True) ∧ (p5 → p2))) ∧ p5) ∨ ((p2 ∧ p4) → p1)) ∨ True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



