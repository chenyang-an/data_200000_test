variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612832120364964654931582665531 : (((((True ∧ ((((p5 ∧ ((p2 ∧ p5) → p4)) → False) ∨ (p4 → (True → p2))) → (((p3 → True) → p3) ∧ p3))) ∨ (p2 → p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_258539562316754392189453188741 : ((p5 ∨ p3) → ((((p3 → (p2 ∨ True)) → p4) ∧ (((p3 → p2) ∧ (p4 ∧ True)) → (p2 → (p3 ∧ p3)))) → ((p2 → (p1 ∧ p2)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156927254404922059953375385555 : ((((p1 → (((False → True) ∧ (p4 → False)) ∧ (((p1 ∨ False) ∨ (p4 → p3)) ∧ p5))) → p4) ∨ p4) ∨ (((p4 ∨ p3) ∨ p4) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157152217609681529252113869143 : ((((((p5 ∨ (p2 ∨ (p1 ∧ p3))) → p3) ∧ ((True → p5) → (p3 ∧ (False → True)))) ∨ p2) → p5) ∨ (p1 ∨ (p4 ∨ ((True ∨ p2) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_350004160906351723341814025605 : (p4 → (((p2 ∧ (((p4 ∨ (p2 ∧ ((p1 ∧ p4) ∨ p4))) ∧ (p2 ∧ p2)) ∧ (((((p1 → True) ∧ p5) → p2) ∨ False) ∧ p2))) ∨ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55539483997493915477129139152 : (((True ∧ ((p4 ∨ p4) → (True → p5))) → (((True ∨ False) → p2) ∨ (True ∧ (p5 ∧ (((False → (False → (p5 ∧ p1))) ∨ False) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227106888925897620815955081865 : (((p4 ∨ False) → p5) ∨ (((((((p2 → p5) → p4) ∨ p3) ∨ ((p1 ∨ True) ∨ True)) ∧ (p2 ∧ ((p4 → p2) → p5))) → p3) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190531764865793458957894129869 : ((((p3 ∨ ((p5 ∨ True) → (False ∨ True))) → p3) → False) ∨ ((True ∨ ((False ∧ p5) ∧ (True → p2))) → (((p1 ∨ (False ∨ p2)) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253016035274186360867589153116 : ((True ∧ p3) → (((True ∨ ((((p4 → p3) ∧ (True ∨ p5)) → (p4 ∧ True)) ∧ p5)) → p1) → (((True → p4) ∨ p4) ∨ ((p4 → p1) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ ((((p4 → p3) ∧ (True ∨ p5)) → (p4 ∧ True)) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197995978134767365018655888301 : (((p5 ∨ p4) ∧ (p4 ∨ (p5 → (False ∧ p4)))) ∨ (p3 → (p3 ∧ ((p5 ∧ ((p1 ∧ True) ∨ False)) → (((False → p1) ∧ True) ∨ (p4 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66181676426184687863657231516 : ((p5 ∨ ((((((p4 ∧ (p3 ∧ (((p5 ∨ p2) ∧ p2) ∧ p1))) ∧ p3) ∨ False) ∨ (p4 ∧ p3)) → p5) ∨ ((p2 ∨ (p2 ∨ True)) ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134143205250698745295050754179 : (((((((((False ∨ p5) → (p3 → False)) → True) ∧ (p3 ∨ p2)) ∨ p1) ∧ (p3 → False)) ∧ ((p4 → p3) ∨ p5)) ∨ p3) ∨ (p1 → (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354911770483346438568021456788 : (p5 → ((False ∨ ((False ∧ (p4 → ((p1 ∧ True) → ((p3 ∨ (p3 ∨ (True ∧ p1))) ∧ ((p2 ∧ False) ∧ False))))) ∧ (p1 ∧ (p3 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157525062321097220747637137897 : (((p3 → ((((p3 → (True → (True ∧ True))) → (p2 → False)) → False) → (False ∧ p4))) ∨ (p2 ∧ p1)) ∨ (False → (((False → p3) ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588831249661103105302511268830 : (((((False ∨ (p5 ∨ ((p2 ∧ p1) ∧ (((False ∧ True) → (p4 → (False ∨ (p3 → p5)))) → ((p1 ∧ False) ∨ (p1 ∧ p5)))))) ∨ p1) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157605840264154276910185256646 : (((((False ∨ (p1 → (p2 ∧ p4))) ∨ ((p3 ∧ (p2 ∨ False)) ∧ p1)) ∧ p1) ∧ (p3 ∨ (p1 ∨ False))) ∨ ((True ∧ (False ∧ (p5 ∨ p1))) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264786033266767964721159606591 : (True ∧ ((True ∧ p2) ∨ (((p2 ∧ True) ∨ (p4 ∨ (p1 ∨ False))) ∨ ((((p1 ∨ (p2 → False)) ∧ p3) ∨ True) ∨ (((True ∨ False) → p1) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53843352311545355965594706631 : ((((p4 → (p5 ∧ (p5 → p3))) ∨ ((p3 ∧ p3) ∧ p4)) ∨ ((True ∧ ((p3 → (p4 → ((p3 ∧ p1) ∧ p5))) ∨ p2)) → (p5 ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587438989342152447094802475170 : ((((((((p1 ∨ p3) ∨ (p2 ∨ ((False ∧ ((p1 ∨ ((p5 ∧ p5) ∨ (p3 ∨ p2))) ∨ True)) ∨ (p4 → False)))) → False) ∨ p4) ∨ True) ∧ True) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39926089719828561358902155951 : (((p3 → ((p2 ∨ ((p2 ∧ p5) ∨ p2)) ∧ (((p1 → (True ∧ p4)) → (False → p5)) ∧ (False ∨ (((p5 ∧ False) ∧ p2) → p4))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157538597352373839117569495229 : (((((False ∨ ((p1 ∨ (p4 → (p3 → p2))) ∨ p5)) → ((False ∧ p5) → p2)) ∨ p1) → (p1 ∧ False)) ∨ ((p2 ∨ (p3 ∨ (False → p3))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351182515240473030794225130445 : (p4 → (((False → p2) ∧ (((((p1 ∨ (((p2 → True) ∧ p5) → False)) → p5) → (False → (p3 → p3))) → p3) ∨ True)) ∧ ((p5 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44478438406093442576721473557 : (((((False ∨ p2) → ((p3 ∧ p2) → ((p2 → (False → p4)) ∨ True))) → (((False ∧ p3) ∨ ((False → p5) ∧ True)) ∧ (p2 → p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_541239327951829278343655052 : ((((p1 ∨ ((p2 ∧ ((p4 ∨ (p1 ∧ False)) → ((p2 → (p5 → (p4 → p1))) ∨ p1))) ∨ p1)) ∨ (False → (p2 → p2))) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608612219255367747552724466182 : (((((((p3 ∧ (True → (p5 → p5))) ∧ (p5 → (p4 → (False ∨ (p1 → (False ∨ (p5 → (True → p1)))))))) ∧ (p2 ∧ p4)) ∨ p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112736984741944773218770896068 : (((((p3 → p3) ∨ (((((p4 ∨ p1) ∧ p4) ∨ True) ∨ False) ∨ p2)) ∧ (((p4 → (False ∧ (p4 ∨ False))) ∨ p5) → True)) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59887450405095313557888247406 : (((p4 ∧ p5) → ((p2 → (True → False)) ∨ (p3 → ((((True ∨ (False → ((p3 ∧ p1) ∧ p1))) ∧ (p5 ∨ p4)) → (p3 ∨ False)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51400948463822426822996925424 : (((((p3 ∧ (False → (False ∨ (((p4 ∨ p1) ∧ (p3 ∨ (p4 ∨ True))) → True)))) ∨ p2) → False) → (((p2 → (p5 ∨ p5)) → p3) → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p5 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 ∧ (False → (False ∨ (((p4 ∨ p1) ∧ (p3 ∨ (p4 ∨ True))) → True)))) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∧ (False → (False ∨ (((p4 ∨ p1) ∧ (p3 ∨ (p4 ∨ True))) → True)))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43833200644337029971507102571 : ((((((p1 ∧ (p4 ∨ (False ∨ ((True ∧ (((p2 → p1) ∨ p5) ∧ ((False ∨ p3) ∧ False))) → False)))) → p1) ∨ p2) ∧ (p2 ∨ p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428955812276337374067343989209 : (((((p4 → (p1 → ((((p3 ∧ ((p5 ∨ False) → ((p1 ∨ p1) → p3))) ∨ True) ∧ (p3 ∨ True)) ∧ p5))) ∨ (True → True)) ∨ (False ∧ p2)) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693853257169813118356038310635 : ((((((p5 ∨ p4) → (p4 ∨ (p5 ∨ (p3 ∨ ((False ∨ p3) → p4))))) → p3) ∨ (p1 → (p1 ∨ (((False ∨ (p1 → p5)) ∧ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60450379184476833969918967809 : (((p5 → False) → (False ∧ ((p3 ∧ ((p5 ∨ p1) → ((p3 → (p2 → p1)) → ((p3 → p1) ∧ (p2 → ((p4 ∨ False) ∨ p1)))))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171452716094050738884372080343 : (((p3 ∧ ((p2 → (((p1 → p5) → False) → p3)) → ((p5 ∧ p1) ∧ p3))) ∧ False) ∨ ((((p2 ∨ False) ∨ ((p1 ∧ True) ∨ p2)) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213091300522643688331241528594 : ((((p5 ∧ p2) ∧ True) ∧ p3) ∨ ((True ∧ (((p5 ∨ (True ∧ p5)) ∨ (True → True)) ∧ (((p2 → (p1 ∨ (False → p1))) ∨ False) → p1))) → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((p2 → (p1 ∨ (False → p1))) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : ((p2 → (p1 ∨ (False → p1))) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h15
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h20 : ((p2 → (p1 ∨ (False → p1))) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- False on the left can always be used.
      apply False.elim h22
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h23 := h5 h20
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190970381148400452033935512613 : (((((p2 ∨ False) ∨ p3) ∧ True) ∨ (p4 ∧ (False ∨ p5))) ∨ (((True ∨ False) → p2) → (True ∨ (p1 → (((p1 ∨ p2) ∨ False) ∧ (p4 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160419422440024999133385874776 : (((((p5 ∨ p2) ∨ (p4 ∨ p1)) → (p5 ∧ ((False → (p4 ∧ False)) ∧ True))) ∨ ((p4 ∨ True) ∧ True)) → (((p5 ∨ p5) ∨ (p2 → True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28253500805220323598976225691 : ((True ∧ ((((p2 ∧ ((p4 → p2) ∧ (p2 ∨ p1))) → False) → ((True ∧ (p3 ∨ p3)) ∨ ((p4 → (p5 → p1)) → p3))) ∨ (p4 → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632381337174009816954771760662 : (((((True ∨ ((p1 ∨ (((False → ((p2 → (p5 ∨ p5)) ∨ True)) → ((p4 → False) ∧ p4)) ∨ p4)) ∧ ((p1 ∧ False) ∨ p2))) → p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49375793975031907715877270820 : (((p5 → ((False ∧ (p1 → (p4 ∨ (p5 → p3)))) ∧ ((((((p4 → p5) ∧ p3) ∧ p2) ∨ False) ∨ p3) ∨ p4))) ∨ (p3 → (True → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165771406095699394549219584098 : (((((p5 ∨ p4) ∨ p1) → p5) → ((((p2 → p2) → ((p5 ∨ True) ∧ p1)) → p4) ∨ False)) ∨ (((p2 ∧ p1) ∨ True) ∨ (p4 ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45801701543719357202454335806 : (((p1 → ((p1 ∧ True) ∧ ((p3 → ((((p3 ∧ True) → ((True → (p2 ∧ p3)) → ((p4 ∧ p4) ∧ p4))) → p5) → p1)) ∧ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156874576738914485752226787218 : ((((p2 ∨ ((p4 ∧ ((p1 ∨ p5) → ((p5 ∧ (False → p2)) ∧ p1))) ∧ (p5 ∨ p3))) ∧ p1) ∨ p3) ∨ (p4 ∨ ((p2 → (False ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249715609259769142226019927237 : ((p5 ∨ p5) ∨ (((((((((True ∧ (p1 ∨ (True ∨ p5))) → p2) ∨ False) ∨ p3) → (p1 ∧ p2)) ∨ p4) ∧ p5) ∨ (p4 → (p4 ∧ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59273846515464743904575071216 : (((p3 ∨ p1) ∨ ((p5 ∨ ((((p4 ∧ p5) ∧ (p2 → p5)) → p1) ∨ p4)) ∨ ((p1 → (((p5 ∨ p4) → (p4 → p1)) ∧ p5)) → True))) ∨ p5) := by
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
theorem thm_5_vars_616744634699404728994293967486 : ((((((((p3 ∧ p4) → p3) → p2) ∨ (False ∧ (False ∧ False))) ∨ (((p4 → True) ∧ (False ∨ (True → p3))) ∧ ((p2 → p4) ∨ p1))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191833640914296399030967501125 : ((p3 ∨ ((p4 ∨ ((p5 ∨ p3) → (p3 → True))) → p1)) ∨ (((p1 ∨ ((p4 ∧ (p3 ∨ (p1 → True))) ∨ (False ∨ p2))) → True) ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711363664491538662194010207018 : ((((p1 ∨ (p1 ∨ ((p5 ∧ p3) → p5))) ∧ (p5 ∨ ((p5 ∨ ((p5 → ((p3 ∨ p1) ∨ p3)) ∨ ((p4 ∨ (p5 → p3)) ∨ p5))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994486610493028099431515731046 : (((p5 ∧ ((False ∨ (((((p4 ∨ p3) ∧ (False ∨ True)) ∧ p4) ∧ (p2 ∧ ((False ∧ ((p2 ∧ p4) → p4)) ∨ (True → p2)))) ∨ True)) → False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (((((p4 ∨ p3) ∧ (False ∨ True)) ∧ p4) ∧ (p2 ∧ ((False ∧ ((p2 ∧ p4) → p4)) ∨ (True → p2)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141462326400011656285037520709 : (((True ∧ (True → False)) ∧ ((((p1 → True) ∧ ((p4 ∨ p2) ∧ ((False → p5) ∧ (True ∧ p5)))) ∧ p1) → (p4 → False))) → (True ∧ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42809100142740070754369417541 : (((p1 → (((p1 → ((((p2 ∨ p2) ∧ p1) ∧ (p3 ∧ (p3 ∨ p5))) ∨ (p3 ∧ ((p4 → p3) ∨ True)))) ∧ (True ∨ p2)) → p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62773301092133916318750486869 : ((p4 ∧ (((True ∨ False) ∨ (((p2 ∨ True) → ((False ∨ p5) ∨ (True → (p1 → p2)))) → (p1 → (p5 ∨ False)))) → ((p2 → p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40348358996657545835577082605 : (((((p5 → ((True → (p1 → (((((p1 ∨ p5) ∨ p4) ∧ (p5 → p2)) ∨ ((p1 ∨ p5) ∧ False)) ∧ p3))) ∨ p1)) ∨ p5) ∨ False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950361113828888450675751829351 : (((((p4 → p4) → False) ∧ ((((((p1 ∧ False) → False) ∨ (((False → p4) ∧ p5) ∨ (False → p2))) ∨ p2) ∨ (p4 → True)) ∨ (False → p4))) → p3) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h8 : (p4 → p4) := by
            -- Implications on the right can always be decomposed.
            intro h9
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h10 := h2 h8
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h15 : (p4 → p4) := by
              -- Implications on the right can always be decomposed.
              intro h16
              -- One of the premise coincides with the conclusion.
              exact h16
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h17 := h2 h15
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h19 : (p4 → p4) := by
              -- Implications on the right can always be decomposed.
              intro h20
              -- One of the premise coincides with the conclusion.
              exact h20
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h21 := h2 h19
            -- False on the left can always be used.
            apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h23 : (p4 → p4) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h23
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : (p4 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h29 := h2 h27
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h31 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h33 := h2 h31
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70021773499383159648005772147 : ((((((((p4 → True) ∨ ((p4 ∧ (p3 ∧ p3)) → True)) → (p5 ∨ p1)) → ((p1 → (p5 ∨ p4)) → (False ∧ p2))) → p2) → p4) ∧ p2) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p4 → True) ∨ ((p4 ∧ (p3 ∧ p3)) → True)) → (p5 ∨ p1)) → ((p1 → (p5 ∨ p4)) → (False ∧ p2))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306423043591170301373022302816 : (p1 ∨ ((p4 ∧ p4) ∨ (((True → (((p3 → ((p3 ∧ p2) ∧ (True → True))) → (p4 ∧ True)) ∧ p5)) ∨ (p5 → p4)) ∨ ((p2 ∧ False) → True)))) := by
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
theorem thm_5_vars_751269633364042336108105279067 : (((True ∧ ((True ∨ p4) ∧ ((((((True ∧ (p2 → ((True → p4) ∨ p5))) → p5) ∨ (p2 → True)) ∨ (p4 ∧ False)) → p4) → (p2 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800275234294547292317330819371 : (((p2 → ((((p1 → (True → (True ∨ p5))) ∧ ((p4 ∧ ((p5 → False) ∧ ((p5 ∧ True) ∧ True))) ∨ (False ∧ True))) ∨ (p5 ∧ p5)) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214170854494872149032914336161 : ((((p5 ∧ p1) → True) → p2) ∨ ((p3 ∨ (False ∧ ((((p4 → p1) → (((False ∧ p2) → p3) ∧ p5)) → p1) ∧ (True ∨ p2)))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346625368664995803297948944021 : (p3 → (((p4 ∨ p4) ∧ ((((((p1 ∨ True) ∧ p2) ∨ False) → (((p1 ∨ p3) ∨ True) ∨ False)) → p2) → (p5 → p4))) ∨ ((p3 ∨ p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117279643113711270752465680978 : ((False ∧ (((True → p2) ∧ ((((p2 ∨ p2) ∧ p5) ∨ (p4 → ((p5 ∧ p3) ∧ p5))) → ((p5 ∨ (p5 ∧ p4)) ∧ p3))) ∨ p1)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318844913528327691544127891509 : (p4 ∨ (((((False → False) → (True ∧ (False ∨ ((p5 ∨ (((p5 → False) → (p2 ∧ True)) ∨ False)) ∨ p1)))) ∨ p1) ∧ p1) ∨ ((p1 ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198920066551171964116950612329 : ((p3 → (p5 ∨ ((True ∧ False) ∧ (True ∨ False)))) ∨ (((True → True) → (p2 ∨ (((True ∨ (p2 ∨ p5)) ∧ p5) ∧ (p2 ∧ p1)))) → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h8.left
        let h17 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h8.left
        let h20 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621288782550556132524518982843 : ((((True ∧ ((p1 ∧ (((True → (p3 ∧ (False ∨ p3))) ∨ True) → (p1 ∨ p2))) ∧ (False ∧ (False → (p3 → ((False ∨ p4) ∧ True)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_940301263963961603543099457547 : (((((((p4 → False) ∨ p5) ∧ False) ∨ True) → (((False ∨ (True → ((p2 ∧ p1) ∧ p4))) ∧ ((p5 ∨ (p2 ∧ (p5 ∨ True))) → p2)) ∧ p5)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → False) ∨ p5) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591143637308187944984505391918 : ((((((((p5 ∨ True) → (p2 ∧ (p1 ∨ ((p2 ∨ p4) → (p3 ∧ p1))))) ∧ ((False ∧ (p4 ∧ p3)) ∧ True)) ∨ True) ∧ (p1 ∧ True)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207043267269851354831848317987 : ((((p4 → p1) → (p3 ∨ True)) ∧ True) → (((True → (((p5 ∧ (p5 ∨ p4)) → p2) ∧ ((p3 → (p2 ∧ p2)) ∧ False))) → (False ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_313113839533829223260067821890 : (p3 ∨ (((p5 → ((p2 → p4) → ((p4 → (((p4 ∨ ((p4 → p2) → p1)) ∧ (p1 ∧ True)) ∧ False)) ∨ p3))) ∨ (False → (p5 ∨ p4))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263704223679852755666334573143 : (True ∧ ((False ∧ ((((p2 → (False ∨ (p3 ∨ p4))) ∧ (p4 ∧ p2)) ∧ (p2 ∧ (True → p1))) ∧ p1)) ∨ (p2 → (p2 ∨ ((False ∨ p1) ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40833185357280358751523812162 : ((((p1 → (p5 ∨ ((((False ∧ (p5 ∨ False)) → ((p1 ∨ (p3 ∧ (p3 ∧ p2))) → (p1 ∨ (p4 → p4)))) → p5) ∧ p4))) → p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175095841953702890400312195024 : ((p3 ∧ (p3 → (p1 ∨ (p5 → ((p2 ∨ ((p2 ∨ p4) → (p2 ∧ False))) ∧ p2))))) → (p4 ∨ (((p3 → (False ∧ p4)) ∨ p3) ∨ (p4 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63182510326308441214857004567 : ((p5 ∧ ((((((p4 ∧ (p5 ∧ (p4 ∨ (False ∨ False)))) ∨ ((p1 ∧ True) ∨ True)) ∧ (p3 ∨ p5)) → p5) ∨ p2) ∧ (p1 ∨ (True ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140916060735905986473803827580 : ((((p3 → True) ∨ (((p5 ∨ (p1 → p2)) → False) ∧ False)) ∧ (((p5 → p4) ∨ (p5 ∧ True)) ∧ (p2 ∧ (True → p1)))) → (p1 ∨ (p2 → p4))) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131709245820198100043333132451 : (((p1 ∨ (p5 → p5)) → (p1 → ((False ∨ ((p3 → True) → (p4 ∧ (p3 ∧ (False → ((p5 ∨ p4) ∨ p1)))))) → p3))) ∧ (False → (p5 ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h13
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- One of the premise coincides with the conclusion.
      exact h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h18
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124032566656331984655054823677 : (((((((p1 ∧ p2) → p3) ∧ (p4 ∧ p1)) ∨ (p2 ∧ p5)) ∨ True) → (p3 → ((p3 ∧ (p5 ∧ p4)) ∧ ((False ∧ p3) ∧ p4)))) → (p3 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p1 ∧ p2) → p3) ∧ (p4 ∧ p1)) ∨ (p2 ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49835647142357125739068680147 : (((p5 → ((((True → ((p2 ∨ ((True → (p4 → (False ∧ True))) ∨ True)) ∧ p5)) → p1) → (True ∧ p2)) ∧ p4)) → ((p4 ∨ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299497903582847360552957652487 : (False ∨ ((p4 → (((p1 → ((p5 ∧ (p1 → p1)) → False)) ∧ False) ∨ (((True → p1) ∨ (p3 → True)) ∧ (((p2 → p1) ∨ p1) → p4)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197792054803952375834778077118 : ((((p4 ∨ True) ∧ p1) ∨ ((p4 ∨ p2) ∧ p2)) ∨ (((p5 → p2) ∧ False) → (False ∨ ((True ∨ ((p3 → p5) → p3)) → (False ∧ (p1 ∧ p2)))))) := by
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
theorem thm_5_vars_678010975283395968572500658348 : ((((((p1 ∨ p2) ∧ (((p5 ∧ p1) ∧ (p5 ∨ (p4 → True))) ∧ (False ∨ p3))) ∧ ((p2 ∧ p3) → p3)) ∨ (p5 ∨ (p4 ∧ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117093350422360104203934515863 : (((p1 → p2) → ((True ∨ (p4 → (((True ∧ p4) ∧ (((p5 ∨ p3) → p5) → ((p2 ∧ p5) → p2))) ∧ (p3 ∨ True)))) → p3)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245967618878640688756386554809 : ((p4 ∧ True) ∨ (((((((p5 → p4) ∨ True) → p4) ∨ (False ∨ ((p1 ∨ True) ∨ False))) ∧ (False → p2)) ∨ p3) ∨ (p1 ∧ (False → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225500946024212771026228410415 : (((p5 ∨ p2) ∧ p1) ∨ ((((False ∨ False) → (p2 ∨ ((p5 ∧ (False ∧ False)) → (True ∨ p3)))) → (p2 ∧ (((p3 ∨ p1) ∨ p1) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943854631400641413052721596825 : ((((p5 ∨ ((p3 ∧ p1) ∨ False)) ∧ (False ∨ (p2 ∧ ((p5 → p3) ∧ (((p5 ∧ True) ∧ (p1 ∨ (((p4 ∨ p4) ∨ True) ∨ p4))) ∨ False))))) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h17 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h18 := h9 h17
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Disjunctions on the left can always be decomposed.
              cases h21
              case inl h22 =>
                -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
                have h23 : p5 := by
                  -- One of the premise coincides with the conclusion.
                  exact h14
                -- We have shown the premise of h9, we can now drive its conclusion.
                let h24 := h9 h23
                -- One of the premise coincides with the conclusion.
                exact h24
              case inr h25 =>
                -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
                have h26 : p5 := by
                  -- One of the premise coincides with the conclusion.
                  exact h14
                -- We have shown the premise of h9, we can now drive its conclusion.
                let h27 := h9 h26
                -- One of the premise coincides with the conclusion.
                exact h27
            case inr h28 =>
              -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
              have h29 : p5 := by
                -- One of the premise coincides with the conclusion.
                exact h14
              -- We have shown the premise of h9, we can now drive its conclusion.
              let h30 := h9 h29
              -- One of the premise coincides with the conclusion.
              exact h30
          case inr h31 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h32 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h14
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h33 := h9 h32
            -- One of the premise coincides with the conclusion.
            exact h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h39 =>
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- Conjunctions on the left can always be decomposed.
          let h48 := h46.left
          let h49 := h46.right
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h50 =>
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h51 =>
            -- Disjunctions on the left can always be decomposed.
            cases h51
            case inl h52 =>
              -- Disjunctions on the left can always be decomposed.
              cases h52
              case inl h53 =>
                -- Disjunctions on the left can always be decomposed.
                cases h53
                case inl h54 =>
                  -- One of the premise coincides with the conclusion.
                  exact h37
                case inr h55 =>
                  -- One of the premise coincides with the conclusion.
                  exact h37
              case inr h56 =>
                -- One of the premise coincides with the conclusion.
                exact h37
            case inr h57 =>
              -- One of the premise coincides with the conclusion.
              exact h37
        case inr h58 =>
          -- False on the left can always be used.
          apply False.elim h58
    case inr h59 =>
      -- False on the left can always be used.
      apply False.elim h59
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157550220560200252425990514362 : (((((((False → (p5 → p5)) ∨ (p5 ∧ False)) → (True ∧ p1)) ∧ p4) ∧ (True → p1)) → (False ∧ p5)) ∨ (((False ∧ (False ∧ p5)) ∧ p5) → False)) := by
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
theorem thm_5_vars_689785901895799311765266422570 : (((((True → (p4 ∨ p2)) → (((p3 → p2) ∨ (p3 → False)) ∨ (True ∨ (p4 ∨ p3)))) ∨ (p3 ∨ (((p3 → False) ∨ p3) ∧ (p4 ∧ p4)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39645369961095620961062355189 : (((p3 ∨ ((((p3 ∧ (False ∧ ((p2 → (p5 → p5)) ∧ p3))) ∨ p4) ∧ (p2 ∨ p2)) ∧ (((True → p5) ∧ (False ∨ p4)) ∧ False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52279728002654264161963398632 : (((p2 → (p4 → ((p4 ∧ ((p1 ∧ p1) ∧ True)) ∧ ((p4 ∨ (p2 → False)) ∨ p5)))) → ((True → False) ∨ ((p2 ∨ True) ∧ (p1 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741514852703398934249797148637 : ((((p5 ∨ p3) ∨ ((False ∨ (p4 ∧ p4)) ∨ ((((True → p3) ∧ (True → p1)) → p5) → ((p4 ∧ True) → (True ∧ ((p1 ∧ True) → p4)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691722051648151613152331464175 : ((((p1 ∨ (((((True → (p2 ∧ p5)) → (p5 ∨ (p2 ∨ p4))) ∧ p3) → True) ∧ p1)) → (((p5 ∨ p4) ∨ (p1 → p2)) ∨ (p1 ∨ p1))) ∨ p4) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69142345744187210934149538898 : ((p5 → (((p3 → (((False ∧ ((p3 → (p4 ∨ False)) ∨ p4)) → p4) ∨ True)) → (True → (p5 ∧ (p4 → False)))) ∨ (False ∧ (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112070900618778217328806988703 : ((((p3 → True) ∧ ((p4 ∧ (p1 ∨ ((p1 ∧ ((p3 ∨ p4) ∨ p4)) ∧ (((p1 → p3) ∧ False) ∧ (p2 → p1))))) ∨ False)) ∨ True) ∨ (True ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801487118103658002371971266168 : (((p2 → ((((p5 ∨ ((True → p3) ∧ p3)) ∧ p4) ∨ p3) ∨ (((p2 → False) ∧ (p2 ∧ ((p1 ∨ p4) ∧ p3))) → ((p3 ∧ False) ∧ False)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h18 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h19 := h11 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h21 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h22 := h11 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h30 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h31 := h23 h30
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h33 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h34 := h23 h33
    -- False on the left can always be used.
    apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134407778425239464169131670720 : (((p1 → ((((p5 → p3) ∨ (True ∨ True)) ∨ (p3 ∨ p3)) → (p1 ∧ (((p2 ∨ p1) ∧ True) → (False ∨ False))))) ∨ p2) ∨ ((p2 → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197587839485515964663631735320 : (((p3 ∧ (p3 ∨ (p4 ∨ p3))) ∨ (False ∨ True)) ∨ ((p4 → (True ∨ (p1 ∧ p5))) ∧ (((p1 ∨ (p4 ∧ p3)) ∧ (False ∧ (True → p1))) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315671791321370278496875208348 : (p3 ∨ ((p5 ∧ False) ∨ ((p3 ∨ p5) ∨ (p2 → (p2 ∨ ((p1 ∨ True) ∧ ((((p4 → p5) ∨ False) ∨ ((p4 → p1) ∨ p5)) ∨ (p1 ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_191825808428917446923722577512 : ((p3 ∨ ((p1 ∧ ((p2 ∧ p1) ∨ (p4 ∨ p3))) ∧ p4)) ∨ (False ∨ ((p2 ∨ (p1 ∨ ((((p1 ∨ p2) ∨ (p1 ∨ p4)) → True) ∧ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300119585581648901336006015981 : (False ∨ (((True → ((p5 → False) ∧ p3)) → (True ∧ ((p4 ∨ p2) ∧ (p3 ∨ (((p5 ∨ p1) ∨ True) ∧ ((p3 ∧ p3) → p4)))))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62570241910162846970993962324 : ((p3 ∧ (True → (True ∧ (((p5 → ((False → (p3 → (p3 ∧ False))) ∧ (p3 ∧ (p3 ∧ (p5 ∨ p1))))) ∧ p1) ∧ (p5 ∨ (True ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345619344670283769375015704032 : (p3 → ((True ∧ ((((((p4 → ((True ∧ p2) → True)) ∨ False) ∨ p4) ∨ ((p2 ∧ p4) ∨ (p2 → True))) → (True → (p2 → False))) ∨ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157464709110762923869426222303 : (((((p3 → p1) → ((p3 ∧ (p2 ∧ ((p3 ∧ False) ∧ (p5 → p2)))) ∧ p2)) ∨ True) ∨ (p3 ∨ p5)) ∨ (((True ∨ p5) ∨ (True → p2)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47659601393392527669726168293 : (((((p5 ∧ (((((True ∨ (p1 ∧ p4)) ∧ (p5 ∧ p4)) ∧ p1) → p2) ∨ p5)) ∨ ((p3 → p2) → (p5 ∧ p1))) ∧ p2) → (p5 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



