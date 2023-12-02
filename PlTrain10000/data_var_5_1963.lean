variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323279840060471587274591610764 : (p5 ∨ ((p4 → (((False ∨ p2) → (((p2 ∨ (p1 ∧ (False ∧ p4))) ∧ (p2 ∨ ((p4 ∧ True) ∨ p5))) ∧ (p3 ∧ p2))) ∨ p2)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300245806196372192949487475388 : (False ∨ (((p2 → p4) ∧ ((((((p4 ∨ (False → p3)) → p1) → ((p5 ∧ p4) → (p3 → (p4 ∨ p3)))) ∨ p2) → False) ∧ p1)) → (p4 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((((p4 ∨ (False → p3)) → p1) → ((p5 ∧ p4) → (p3 → (p4 ∨ p3)))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : ((((p4 ∨ (False → p3)) → p1) → ((p5 ∧ p4) → (p3 → (p4 ∨ p3)))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h23 := h15 h17
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54481646688508810763468923765 : ((((p1 ∧ (p2 ∧ (p4 ∧ False))) ∨ (p1 ∨ p1)) ∨ ((((False ∧ (True ∧ False)) ∧ True) → ((((False ∧ p1) → True) ∨ p3) → True)) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_37536857123121589978990713230 : ((((p3 ∧ ((p1 ∨ (p4 → p5)) → (((((p5 ∨ p3) ∨ True) → p2) ∨ (False ∧ (p1 ∧ (p5 → p2)))) ∧ (False ∨ p4)))) ∨ False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225261790783875169633036513765 : (((True ∨ p1) ∧ p4) ∨ (((p1 → p4) ∧ (((False ∨ (p4 → p4)) ∨ p3) → (p3 ∧ ((p5 ∨ p1) ∧ p2)))) ∨ (True ∧ ((p3 ∧ p4) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219439869096927434827804963037 : ((p4 ∨ ((p2 ∧ p3) → p2)) → (((((p2 ∨ True) ∨ True) ∨ p5) → False) ∨ (((p3 ∨ ((p1 → (p2 ∨ p4)) ∧ True)) ∧ (p3 → False)) ∨ True))) := by
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
theorem thm_5_vars_261573127743592533823210220641 : ((p5 → p4) → (((p5 ∨ (((False ∧ True) ∨ p1) ∧ p1)) ∨ ((((p1 → p3) → (p3 → (p3 ∨ p2))) ∨ p5) ∨ p4)) ∨ ((True ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137941177117433713466729106282 : ((p5 ∨ ((((p5 ∨ ((((((p2 ∨ p2) ∨ p2) ∧ p3) → p3) ∧ (True → p2)) ∧ (True ∨ p2))) ∧ p4) ∨ p2) ∧ p5)) ∨ (False → (p1 ∧ True))) := by
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
theorem thm_5_vars_115567161005484236239550799113 : ((((((False → p1) ∧ False) ∧ p1) → False) ∧ (((True ∧ ((p3 ∧ (p5 ∨ p3)) ∨ True)) → (True → p4)) → (p1 → (p2 ∨ p1)))) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55395708572918019551719137902 : ((((p5 ∨ (p4 → (p3 ∨ False))) ∧ p4) → ((p3 ∧ (p3 ∨ (p2 ∧ p2))) ∨ (((p4 ∧ p2) → (p3 → False)) ∧ ((p4 → p4) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42129993093813888456693008024 : ((((p1 ∨ p5) → ((p3 → ((p4 ∨ ((p1 → ((p4 ∨ True) → (p2 → ((p4 ∨ (p4 ∧ p5)) ∨ p3)))) → p3)) → p4)) ∨ p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204148831051956641562171509490 : (((((p2 ∨ p3) ∧ True) ∨ p5) ∧ p1) ∨ (((p3 → ((p5 → (False ∧ p1)) ∨ p2)) ∧ p4) → ((p1 → ((p5 ∨ p5) ∨ False)) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_962415905312087197601364505988 : ((((True → False) ∧ ((True ∧ (p4 ∧ p1)) → (p4 ∧ (p4 → (p3 ∧ ((((p3 → ((p3 ∧ False) ∧ p4)) ∨ p3) → (p2 ∨ p5)) ∨ p1)))))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871317968494697133841663691095 : ((((p2 ∨ (((True ∨ p5) → (((p4 → p1) ∧ (False ∨ (p5 ∨ (False → p4)))) ∧ (p2 ∨ ((p4 → (p1 → True)) ∧ False)))) ∨ True)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((True ∨ p5) → (((p4 → p1) ∧ (False ∨ (p5 ∨ (False → p4)))) ∧ (p2 ∨ ((p4 → (p1 → True)) ∧ False)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308354455829860032430452281345 : (p2 ∨ ((((p4 → p5) ∨ ((False ∧ ((p5 → ((p4 → (((((p5 → p4) → p5) → p1) → p3) ∨ p1)) ∨ p3)) → p5)) ∨ p3)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649552192480323578064667629329 : (((((((((True → p5) → p3) → (((True ∨ p4) ∧ (p4 ∨ (p3 → p3))) ∧ (False ∧ p5))) → False) ∧ p3) ∨ (True ∨ p3)) ∧ (False ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351242622696406496315616164668 : (p4 → (((p5 ∨ (p2 ∨ (p5 ∧ p3))) ∧ (((((p4 → True) ∧ ((p5 → (p4 → p2)) ∧ False)) ∧ p4) ∧ p5) ∧ p4)) ∨ ((p4 → p4) ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158509710163117186550431344930 : (((False ∨ p4) → (((p3 ∨ (False → False)) ∧ p2) ∨ (((p4 → p4) ∨ ((p5 ∧ True) ∨ True)) → False))) ∨ (False → (False ∧ ((False ∧ p5) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213976318606980164085290545021 : (((p4 → (p1 ∨ p1)) ∨ p4) ∨ ((p3 ∨ ((p2 ∨ p3) ∨ p5)) ∨ (p3 ∨ ((((p1 ∨ p2) → p5) ∧ (True ∧ (p4 ∧ p4))) ∨ (p1 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301133975627925117749613146444 : (False ∨ (((((p5 ∧ (p3 ∨ p3)) ∨ p4) ∧ p3) ∧ True) ∨ (((p5 ∨ True) → (((True ∧ True) ∧ (p3 ∨ ((p3 ∨ p2) ∨ False))) ∧ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683537280160185191117641278756 : ((((p5 → ((p1 ∧ (False ∧ ((p4 ∨ p5) ∧ ((p4 → p2) → (False ∨ True))))) ∧ (p4 → p1))) ∧ ((p1 ∧ ((p1 ∨ p1) → p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172478424035771867204435359589 : (((((p1 → p2) → p3) → p3) → (((p3 → (p1 → p3)) ∧ (p2 ∧ p2)) → False)) ∨ (p1 → (((p4 ∧ True) ∧ (p2 → (p2 ∨ False))) → p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341107057773364274778407306787 : (p2 → ((p4 → (False ∨ (((True ∧ ((((p3 ∨ p5) ∧ p2) ∨ p1) → ((p4 → False) → (False ∧ (p1 → (p5 ∧ True)))))) ∨ p4) ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700633709950252225377911060107 : ((((p2 → (p3 ∨ ((p4 ∧ (p5 → p2)) ∨ (p4 ∧ (p2 ∨ p1))))) → ((((p4 → p5) → False) ∧ p2) ∨ (p4 → (False → (True ∨ p1))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158918269922177885166593526279 : ((p1 ∨ (p2 ∧ (((False → p1) → ((((((True → False) → p5) ∨ p2) ∧ False) ∧ True) ∨ p5)) ∧ True))) ∨ ((p5 ∨ ((False → p1) ∨ p3)) ∨ p4)) := by
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
theorem thm_5_vars_262171458847722491034322468908 : (True ∧ (((p5 ∨ ((p5 ∧ (p3 → ((((False ∧ (p1 ∨ (p3 ∧ False))) → (p1 → p3)) → p1) ∨ p2))) ∧ (p2 ∧ (p4 ∧ p4)))) ∨ True) ∨ p3)) := by
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
theorem thm_5_vars_193409618464191599614790578389 : (((True ∨ p4) ∧ (p4 ∨ (p3 ∨ (False ∨ (False ∨ p2))))) → (p4 ∨ (((p2 → False) ∧ (False ∨ (p2 ∧ p5))) → (p3 ∨ ((p1 ∧ p3) ∧ p1))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- False on the left can always be used.
              apply False.elim h23
            case inr h24 =>
              -- Conjunctions on the left can always be decomposed.
              let h25 := h24.left
              let h26 := h24.right
              -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
              have h27 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h25
              -- We have shown the premise of h21, we can now drive its conclusion.
              let h28 := h21 h27
              -- False on the left can always be used.
              apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h30 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- False on the left can always be used.
            apply False.elim h36
          case inr h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306150294772496780974676933165 : (p1 ∨ (((p4 → True) ∧ p4) ∨ ((((((p2 → p4) → p4) ∧ True) ∧ (p2 ∧ (p1 ∧ (p2 ∨ (p1 ∨ p3))))) ∨ True) ∨ ((p4 ∨ p4) → p1)))) := by
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
theorem thm_5_vars_248021427625571991500297014656 : ((p1 ∨ p5) ∨ (((True ∧ ((p3 → ((((p2 ∧ p4) → p3) → p4) → True)) ∧ True)) → (((p5 ∨ p3) ∧ ((p1 ∧ False) ∧ p2)) ∧ False)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((p3 → ((((p2 ∧ p4) → p3) → p4) → True)) ∧ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4620766786587704487594787772 : (p4 → (p2 → (((((p1 ∨ True) ∨ p5) → p4) → ((((p2 → p1) ∧ (True → p1)) ∧ (((p5 ∧ False) ∨ p4) ∧ p1)) ∧ p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678793179861290227609577371579 : ((((True ∧ ((((False → p5) ∨ p3) → (p1 ∨ (True ∧ (True ∧ p1)))) ∧ ((p4 → (p1 → p1)) ∧ p5))) ∨ (True → (False → (p4 ∧ p3)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123591843274093080355673274531 : (((((p4 → p3) → p3) → (((((p2 ∧ (p1 → False)) ∧ p1) → p5) ∨ True) ∨ True)) ∨ (((p2 ∨ p3) ∧ (False ∨ p4)) ∧ p1)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337101270134539731229545732721 : (p1 → (((p1 ∨ ((p4 ∧ p5) → p5)) ∧ ((((p5 → (p5 ∧ p3)) ∧ p4) ∧ p1) → (((False ∧ p4) ∧ (p3 → p3)) ∨ p3))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673389619133439371243257101232 : (((((((False → p1) → (False ∧ p3)) ∨ True) → (((p3 ∧ (((p4 ∨ True) ∧ p2) ∨ p3)) → (p4 ∧ False)) → True)) → ((p5 ∨ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40335564117207964131220574125 : ((((((((p3 ∨ (p1 ∨ (p3 ∨ p5))) ∧ (False → p5)) ∧ p2) → ((p2 ∨ (p1 ∨ (p5 ∨ (False ∧ p3)))) ∧ p5)) ∨ p1) ∨ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71046802594170640696281850369 : ((((p5 ∨ (((p3 → p2) → False) ∧ p4)) ∧ ((((p3 ∧ ((p2 ∨ (p2 ∧ True)) ∨ True)) ∧ p4) → (p3 ∨ (True ∧ p3))) → p1)) ∧ p2) → p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p3 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39120751328556430302108959900 : ((((True ∧ p4) → ((p3 → (((True ∨ (p5 ∧ p4)) → p5) ∨ (p2 → (((False ∧ p2) → p4) → p5)))) ∧ ((True ∨ True) ∧ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116952997739608919052608416382 : (((p2 ∧ p4) → (((p1 ∨ (((p1 → False) ∨ (p4 ∧ ((p2 ∨ (True ∨ p3)) ∨ p5))) → (False ∨ p1))) ∧ (p5 ∨ p4)) ∨ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779663278008884264173731866306 : (((p2 ∨ ((((((((p2 ∧ p5) ∧ ((True → ((False ∨ p1) ∧ True)) → p5)) ∧ (p1 → p4)) ∨ p2) ∧ (p2 ∧ p3)) → True) ∨ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41473954197216350004217877485 : (((((p4 → (((True → (True ∨ p2)) ∨ (p1 ∧ p5)) → True)) → p3) ∨ (p4 → ((p4 ∧ (p1 ∨ True)) ∨ (p5 ∨ (p5 ∨ p3))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634092025734441081391373493368 : (((((((((p1 ∧ p1) → (p4 ∨ p4)) ∨ p2) ∨ p2) → ((p3 → (((p3 ∨ p3) → True) ∨ p4)) → (p1 ∨ p4))) → (p4 ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686676123510713915773265233365 : (((((p1 → p2) → ((((p2 ∨ (p3 ∨ (False ∨ p5))) ∨ (p5 ∨ p1)) ∨ p4) → (p5 ∨ True))) → (((p4 → p5) ∨ p5) ∨ (p1 ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119338191286091620684015159163 : ((p3 → (((True ∨ (True ∨ True)) ∨ True) → (((p2 ∨ ((False ∨ (False ∧ True)) ∧ (p3 ∧ (p2 ∨ True)))) ∨ p2) ∧ (p2 ∨ True)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246701561840767471939508842808 : ((p5 ∧ p4) ∨ ((((False ∨ p3) ∨ p1) ∧ ((p3 → (p5 ∨ (True ∧ p3))) ∨ p1)) → (((True → False) ∨ p3) ∨ (((True ∧ p1) ∨ p3) ∨ False)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
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
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
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
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246443674978495441305689898639 : ((p5 ∧ False) ∨ (((True ∨ False) → ((p3 ∧ (((((p2 ∧ p1) ∨ p5) ∧ (p5 → (True ∨ (p3 → False)))) → False) ∧ (p5 → p1))) ∧ p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113303790585884632024216606692 : ((((p1 ∨ (True ∨ ((p2 ∨ p3) ∨ True))) → (p2 → (False ∧ ((p4 → (False → p3)) → (True → (p5 → p2)))))) ∧ (True ∨ p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656485872785562343784473434102 : ((((((p1 ∧ ((p1 → p5) ∧ ((p1 ∧ p3) → p5))) ∨ p4) → ((False ∧ (p1 → (((p5 ∧ p5) ∨ p3) ∨ p3))) ∨ p1)) ∨ (False → p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_158592445792302496883942779328 : ((False ∧ ((((p2 ∨ (True ∨ (p4 ∨ p1))) ∨ (p3 ∨ ((p3 → False) ∨ False))) → (p2 ∧ False)) ∧ p2)) ∨ (False → ((p4 ∧ p5) → (p2 → p1)))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345575444936527171180736329755 : (p3 → ((((p4 ∧ p3) → p5) ∨ ((p2 ∨ p4) ∨ ((p1 → ((p1 → (False ∧ (p2 ∧ (p1 ∧ True)))) → (p3 → (False ∧ p2)))) ∧ p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606333085217958489542491072250 : (((((((((p1 → (p5 ∨ ((p4 ∧ ((p4 → p2) → True)) ∧ p1))) ∧ ((p1 ∧ p1) ∨ (p2 ∧ p5))) → p5) → p2) ∨ False) ∧ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_134934979006736117365288363379 : ((((True → (p5 ∨ (False ∧ ((p5 ∨ ((p5 ∧ ((p5 ∨ p5) ∧ True)) ∨ (p3 ∨ p2))) ∧ p5)))) → p3) ∧ (p4 ∨ p4)) ∨ (p4 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261558747553500169542204429753 : ((p5 → p4) → (((p1 ∧ ((True ∨ True) ∧ ((p1 ∨ True) → p5))) ∨ (((p4 ∨ (p1 → (p3 → p2))) ∨ p1) ∨ ((False ∨ p2) ∨ True))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102087206526008099752449849479 : ((((p1 ∧ ((p2 ∧ p5) ∨ (((p1 → False) ∧ (False ∨ (True ∨ (p5 ∧ (p5 ∧ p4))))) → p4))) ∨ ((p1 ∨ True) ∨ False)) ∧ True) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172976852274806844353865999716 : ((p4 ∧ (p2 ∧ ((((True → p5) ∨ p5) ∧ (p1 ∨ (p4 ∨ (p3 ∨ p5)))) ∨ True))) ∨ ((p2 ∨ True) ∨ ((p5 ∨ p2) ∨ ((p5 → p1) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695862245128761243113595936418 : (((((p3 → p1) ∧ ((False ∨ (p5 → p5)) → ((True ∨ p5) ∧ (p3 ∧ p1)))) → (p3 ∨ ((p1 → (p4 ∨ ((p3 ∧ p5) → p3))) → p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179712245841110955742580657378 : ((((True → ((((p5 ∨ p1) → p3) ∨ True) ∨ (p2 → True))) ∨ p4) ∧ p3) → (((p1 ∨ (True ∧ (((p1 → p1) ∧ p4) → p1))) → p5) ∨ True)) := by
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
theorem thm_5_vars_310309932080822661139327635131 : (p2 ∨ ((p3 ∧ ((p1 → (((p1 ∨ p2) ∧ p1) → p2)) → p4)) ∨ ((((p4 → ((p1 → p2) ∧ ((p2 ∨ True) → True))) ∨ p1) → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200186543359175224578751579075 : (((p4 ∧ (True ∨ p2)) ∨ ((p3 ∧ True) ∧ p3)) → (p1 ∨ ((False ∧ (((p1 ∨ p5) ∧ (p2 ∨ (False ∧ (p4 ∧ p2)))) → True)) ∨ (False → p2)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119238663690989810324023535092 : ((p2 → (False ∧ (False ∨ (((((False ∨ (False → (p2 → p2))) ∨ (p4 ∨ True)) → (p2 → (p1 ∧ (False → False)))) ∨ p3) ∧ False)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180551105930509047635509522599 : (((p5 ∨ ((p4 ∧ (False ∨ p5)) → (p4 ∧ p3))) ∨ ((p5 → True) ∧ p3)) → ((p5 → p2) ∨ (True ∨ (False ∧ ((p2 → p5) ∨ (p2 → p5)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47388064957397677323843749577 : ((((True → p1) → ((p2 → p4) ∨ (((p4 ∧ ((p5 ∨ (p3 ∧ (p2 ∧ p5))) ∧ p3)) ∨ (False → p3)) ∧ (p2 → p4)))) ∨ (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42618564953049128490678169115 : (((p3 ∨ (((((p5 ∨ (p5 ∨ (p5 → (p2 ∨ (p3 → True))))) ∨ False) ∨ ((False ∧ p1) ∨ p1)) ∧ p4) ∨ ((p2 ∨ True) ∨ p1))) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41967643631758090700746431930 : ((((True ∨ p3) ∧ (p1 ∨ ((True ∧ (((p4 ∧ (p1 → (p5 → p1))) → (p4 → p1)) ∨ False)) ∨ ((p4 ∨ (p4 → p4)) → p1)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263621504984704607256972519123 : (True ∧ (((p4 ∧ (p3 ∨ False)) ∨ ((False ∨ (p1 ∧ (p4 → p5))) ∨ ((True ∧ p1) → (p2 ∧ (False → p5))))) → ((p5 ∨ p5) → (p5 ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137051402606952750782417802379 : (((p1 → False) → (p4 ∨ ((p5 → p1) → (p5 → (((p1 ∨ p3) ∨ (((p2 ∨ p5) ∧ (False ∨ False)) ∨ False)) ∨ p2))))) ∨ (p5 ∧ (p1 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181469308809817058413785909387 : ((p4 ∨ ((p4 → ((True → p2) → (True ∨ p5))) ∧ ((True ∨ p1) ∧ p2))) → (p5 ∨ (p1 ∨ ((False ∧ (False ∧ False)) → (p3 ∨ (False ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397500249128942319167452950627 : ((((p2 ∨ (((p1 ∧ (((((p1 → False) ∧ ((p4 ∨ p3) ∧ p3)) ∨ p1) ∨ False) ∧ p5)) ∨ True) ∨ (((p2 ∧ p3) → False) ∨ p5))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59542233779192942040946424826 : (((p3 → False) ∨ ((((True → False) → (((p2 → p1) ∧ (p5 ∧ p3)) → p3)) ∨ (p1 ∨ (True ∨ (p3 ∨ ((p5 ∧ p5) ∨ p4))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199072083693773297164433400828 : ((((((p5 ∨ p3) → p1) → True) → True) ∧ p3) → (((True ∨ False) ∧ ((((p1 ∧ (p2 ∧ False)) ∨ (p5 → (p3 ∧ p2))) ∨ p3) ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350047081428578629600420424047 : (p4 → (((p2 ∨ ((False ∧ (((p2 ∧ ((False ∧ p1) ∧ True)) → (p1 ∨ (p3 ∨ (p4 ∨ (p3 ∧ (p5 → p2)))))) ∨ p5)) → p2)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803492743035236079578703870745 : (((p3 → (((((((p1 ∧ (p3 ∨ (p1 ∧ p2))) ∧ (p3 ∨ (p4 ∧ (p1 ∧ (p2 ∧ False))))) ∨ True) → (p4 ∨ p4)) ∨ p4) → p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137095216508210298245416690939 : ((True ∧ ((((p4 ∧ p4) ∧ ((p4 ∨ (((p3 ∧ False) ∧ p4) ∨ (p2 → p2))) ∧ (p5 → p5))) ∧ (p3 → p4)) → p2)) ∨ ((p2 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56760318717131431891316959096 : ((((p4 → p2) ∨ p2) ∧ (p5 ∧ (p2 ∧ (((((p1 → p3) ∨ p2) ∧ (((p3 ∨ ((p2 ∨ True) → p4)) → p5) → False)) ∧ p2) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388322586865828755532902554905 : (((((p5 ∨ (p3 ∨ (p4 ∧ ((False ∧ p5) ∨ (p2 ∨ (((p4 → p2) → (p3 ∨ p5)) ∨ False)))))) ∨ (p4 ∧ ((True ∨ p3) → p3))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_314104054877540781189077461219 : (p3 ∨ (((p5 ∧ (p2 ∨ (p1 ∨ p4))) ∧ (True ∧ ((p2 ∨ (((False ∧ True) ∧ p5) → (p4 ∨ (p1 ∨ True)))) ∧ (p5 → p1)))) → (p1 ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h3.left
      let h23 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h28 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h29 := h25 h28
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592403517838937807245582371900 : ((((((((True → p5) ∨ (((p3 → p3) → p5) ∧ p4)) ∨ (p5 ∧ p4)) → (((p5 → (True ∧ True)) ∨ True) ∧ False)) → (p1 ∧ True)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55625752063255779905407997487 : (((p4 → (p3 → (p5 → (p3 → p2)))) → (((((p4 ∧ p1) ∧ (p1 ∨ (p5 → (False ∨ p1)))) ∧ p3) ∨ True) ∨ ((p5 ∧ True) ∨ p4))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201011041296577206397991891503 : ((p3 ∨ (p2 ∨ ((False ∧ (False ∨ p5)) ∧ True))) → ((((p2 ∧ p2) ∨ (p4 ∨ p4)) ∧ (p2 → p4)) → (p5 ∨ (True ∧ (p4 ∨ (p1 → p4)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- False on the left can always be used.
          apply False.elim h28
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- False on the left can always be used.
          apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350125764149048298190789229526 : (p4 → ((((((True ∧ p5) → (True ∨ ((p4 ∨ ((p3 → p2) ∧ True)) ∧ False))) ∧ p3) → p1) → ((((False ∧ p1) → p2) ∧ p2) → p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172408766706501299833833106453 : ((((False ∧ (p1 ∧ True)) ∧ p1) ∧ (((False ∨ p3) ∧ False) ∨ (False ∨ (p5 ∨ p5)))) ∨ (p2 → (p5 → (p1 → ((False ∧ (p4 ∨ p5)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303418951206806886416833117873 : (p1 ∨ (((p4 → ((((((p5 ∧ (True ∨ (p4 ∨ p2))) ∧ p4) → p2) ∨ p2) → p2) → ((p5 → (p1 → p3)) ∧ False))) ∨ (p4 → p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53925577221045004642773476984 : (((p4 ∨ ((((p3 ∧ p5) ∧ (p2 ∨ p5)) ∨ p3) ∨ p4)) ∨ ((p4 → (p3 ∨ ((False ∨ (True → p4)) ∧ p3))) → (False → (p1 → p4)))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44016434112872945911958526938 : ((((((p5 → (((p4 ∧ (False → p2)) ∧ p3) → p3)) → p2) → (((p1 ∧ p4) ∧ p1) ∨ (p4 ∧ (p2 ∨ p5)))) → (p2 ∧ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257211120968916667144260207606 : ((p2 ∨ p2) → ((p1 → ((False ∧ (p4 → p1)) → p5)) ∧ ((False ∨ (p5 ∨ False)) ∨ ((p2 ∧ (True → p4)) → (((p3 ∧ p3) ∨ p4) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165790030781738942857148156646 : (((p1 → ((p1 → p5) ∧ p1)) → (((((p4 ∨ p5) → p4) ∨ p1) ∨ (True ∨ True)) ∨ p2)) ∨ ((False ∨ (True ∨ p5)) ∧ ((p2 ∨ p3) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68666944198657602027309725558 : ((p4 → ((p4 ∧ (((p5 → False) ∧ (((p1 ∨ False) ∧ ((p3 ∨ (p1 → p4)) ∧ p5)) ∧ p1)) ∧ (p1 ∨ (True ∨ (False → True))))) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h17 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h19 := h7 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h22 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h23 := h7 h22
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h25 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h26 := h7 h25
          -- False on the left can always be used.
          apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h28 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h29 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h30 := h7 h29
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h33 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h34 := h7 h33
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h36 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h37 := h7 h36
          -- False on the left can always be used.
          apply False.elim h37
  case inr h38 =>
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218076314182039727092419211639 : (((p5 ∨ p2) ∧ (p2 ∧ p3)) → (p1 ∨ ((((((p4 ∧ p3) ∧ (False ∧ (False → p3))) ∧ p5) ∨ p5) ∨ ((p1 ∨ (p4 ∧ p3)) ∧ p5)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694762064199835929035463557630 : ((((p5 ∨ (((p3 ∨ ((p5 → p4) → (p1 ∧ p1))) ∨ (p5 ∨ p4)) ∧ p4)) ∨ ((p2 ∨ (True → True)) ∧ ((p2 ∧ p5) ∨ (False → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40940943686303881416437055327 : (((((((p5 ∧ (p2 ∨ ((True ∨ (p2 → ((p3 ∧ p3) → True))) ∧ True))) → ((True → p2) ∧ p1)) ∨ p1) → p3) ∨ (True ∧ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696117430662899121154084073960 : ((((True ∨ ((p5 → (p3 ∨ True)) ∨ (True ∧ ((p5 → (p2 → True)) ∨ p3)))) → (((p3 → False) → False) ∧ ((p3 → (p3 → False)) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61425947023199511316862885349 : ((p1 ∧ (((((p5 → p1) ∨ p5) ∧ (p4 → ((True ∧ p2) ∧ ((p4 → (True ∧ True)) ∧ True)))) → (((p4 ∧ p1) → True) ∧ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105318927794161216943660006448 : (((p3 ∨ (p3 ∨ ((p5 → False) ∧ ((((((True ∧ False) ∧ p3) ∨ p5) → (p3 → p1)) ∨ False) → p3)))) → (p3 ∨ (p1 ∨ p2))) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (((((True ∧ False) ∧ p3) ∨ p5) → (p3 → p1)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h17 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h18 := h6 h17
          -- False on the left can always be used.
          apply False.elim h18
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h19 := h7 h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238192385875704669696524956306 : ((True ∨ p4) ∧ ((p1 ∧ (((((p2 ∨ p2) ∧ p4) ∨ (p4 ∨ (p5 → ((p5 → (p4 ∨ p5)) ∨ p3)))) ∨ p1) → p1)) ∨ (True ∧ (p1 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_342014175561405270320370891158 : (p2 → ((False ∨ (((((True → False) ∧ p1) ∨ p2) ∧ True) → (p1 ∧ ((p3 → (p3 ∨ p3)) ∧ (False ∨ (p3 ∧ p2)))))) ∨ ((p5 ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353896971238061205078687185588 : (p4 → (p2 → (((p5 ∧ ((False → ((False ∨ (((False ∧ p3) ∨ (True ∧ p3)) ∨ p3)) ∧ p4)) → (False ∧ (p5 ∧ p4)))) ∧ (p3 → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232077865688659706807782257338 : (((p4 ∨ p2) → p5) → ((p3 ∧ ((((False → p1) → p3) ∨ (p3 → (p2 ∧ p2))) → False)) → (((p5 → p1) ∧ (p3 ∨ p2)) ∧ (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((False → p1) → p3) ∨ (p3 → (p2 ∧ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : (((False → p1) → p3) ∨ (p3 → (p2 ∧ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h13
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192662901171787818333746695642 : (((((False → (p4 ∨ p5)) ∧ (p1 ∨ p3)) → True) → p4) → (p4 ∨ (p5 → (p1 ∨ ((p3 ∨ (p4 ∨ (p2 ∧ p4))) ∧ (p5 → (p1 → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (p4 ∨ p5)) ∧ (p1 ∨ p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56910174163477139454505729740 : (((p5 ∧ (p1 ∧ True)) ∧ (((p5 → (p5 ∨ (p1 → p4))) → p3) → (p1 ∧ (p2 ∧ ((p5 ∨ ((p3 ∨ (p3 ∨ p3)) ∧ p1)) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158184148980594735836484881423 : (((True ∨ ((True → p3) ∨ p5)) → (p5 → ((p2 ∧ (((p1 ∨ False) ∧ (True ∨ p4)) ∧ p2)) ∨ p2))) ∨ ((False ∨ True) ∧ (p5 → (p4 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208035396357382527768724531735 : (((p1 ∧ (p5 → p3)) ∨ (p1 ∨ p4)) → (True ∧ (((((p2 → p2) ∧ (p3 ∨ p5)) → p4) ∧ (False → False)) ∨ (True ∨ ((p2 ∧ p3) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



