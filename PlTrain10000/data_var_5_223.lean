variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58579507458318539416219559616 : (((True → p4) ∧ ((((True ∧ p4) → (((((p4 ∨ (p1 ∨ p5)) ∧ (((True ∨ p3) ∧ p3) ∨ p2)) ∧ p5) → False) → p5)) → p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187531556841542419092160188895 : ((p1 ∨ (p2 → ((p1 ∧ ((True ∨ (p4 ∨ p4)) ∧ p5)) ∧ False))) → ((((((p2 → p5) ∧ p2) ∨ p5) → ((p2 → p5) → False)) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_207810402124633632591896571315 : (((p2 → (False → (True → p1))) → p5) → ((p1 → ((True ∧ (((((False ∨ False) → p2) ∨ False) → ((True ∨ False) ∧ False)) ∧ True)) → p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (((False ∨ False) → p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h8
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194232208430559295806737211532 : ((p4 → ((p1 → ((p3 → (p2 ∧ False)) → p3)) ∨ p2)) → (((False → False) ∧ (p5 ∨ (((False ∧ False) ∧ (p1 ∨ p2)) ∨ p2))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171515680372599629337030639610 : (((((p5 ∧ True) ∨ ((((p2 ∧ p2) → (False ∧ p3)) → p4) → p1)) ∧ p5) ∨ p4) ∨ (p3 → (p4 ∨ ((True ∨ ((p5 ∧ False) ∧ p1)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806806643991029612057482382699 : (((p4 → ((((p5 ∧ (p5 ∧ ((p4 → p5) ∨ p3))) → p3) → ((p4 ∨ ((p5 → True) ∧ p3)) ∧ ((p1 ∧ p4) ∨ False))) ∨ (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712725479529962994680502892919 : (((((p1 ∧ False) ∨ (p4 ∨ (False ∧ p3))) ∨ ((p5 ∧ p1) → ((False → False) ∧ ((((p3 ∧ (p4 → p3)) → p2) ∨ (p2 ∨ p1)) ∨ p1)))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591448630440489462140184958798 : ((((((p5 ∧ p3) → ((True → p5) → ((((p5 ∧ False) ∧ p1) ∨ (p1 ∧ ((False → (p3 → p2)) → p3))) ∧ p5))) ∧ (p5 ∨ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171327398576867870242397434313 : (((((True ∨ p4) → (((p2 → (False → p5)) ∧ True) → (False ∨ p3))) ∨ p2) ∧ False) ∨ ((p5 → ((p4 ∨ p5) ∨ p5)) ∨ (False → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59628748715445061044923456252 : (((p5 → p1) ∨ (((p2 → False) → p2) ∨ (True → (((True ∧ (p1 → p5)) ∨ (False ∨ True)) ∨ (((p3 ∧ p4) ∨ (p5 ∧ True)) ∧ p2))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47251525594753278856217784973 : ((((((p5 ∨ p3) ∧ (False ∨ p5)) ∨ p1) ∨ (True ∨ (False ∧ (((False ∧ (True ∨ (p2 → p3))) ∨ True) ∨ (p1 ∧ p1))))) ∨ (p5 ∨ p1)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610725695122948178730730466693 : (((((((p4 ∧ (p5 ∨ ((((True → p4) ∧ ((False ∨ True) → p4)) ∨ (p1 → False)) ∨ p2))) ∧ p4) → (p3 ∨ (p4 → p1))) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_198700921617318208903078767113 : ((p5 ∨ ((((p3 → p1) → p2) ∧ p4) ∧ p2)) ∨ (((True → (p3 ∧ p3)) ∨ (False ∨ True)) ∨ (p5 ∧ ((p1 ∧ (p1 → p4)) ∧ (p1 ∧ p1))))) := by
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
theorem thm_5_vars_43815423461442812331630701062 : ((((p3 → ((p1 → False) ∧ (False ∨ (((p4 ∨ (p3 ∧ False)) ∧ ((p2 ∧ (False ∨ p5)) ∧ (p1 ∨ (p3 → p3)))) ∨ True)))) → p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62535442761433263542158489545 : ((p3 ∧ (False ∨ (((((p4 ∨ p3) ∧ p2) → False) ∧ True) ∧ (((p5 ∧ p5) ∨ p4) → (((((p5 ∧ p4) ∨ p5) ∧ p4) → p3) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54250352051619906762204387686 : ((((((p2 → p1) → p1) ∨ p2) ∨ (p1 → p4)) ∧ ((p2 ∨ (p5 → (((p2 → ((True ∨ p1) → p1)) ∧ p5) → (p4 ∧ p5)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347383236285310223015179150247 : (p3 → (((p3 → True) ∧ ((p5 → p2) ∧ (False ∧ p5))) ∨ (p5 ∨ ((((p1 ∨ p1) ∧ (p3 ∧ (p2 → p2))) ∧ (p2 ∧ (p5 → p4))) ∨ True)))) := by
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
theorem thm_5_vars_245451172611309692573636703304 : ((p2 ∧ p4) ∨ (p5 ∨ (p5 → (((p1 → p5) ∧ ((((p4 → (p5 ∧ True)) ∧ p5) ∧ (False ∨ False)) ∧ (p3 → (p2 ∨ p2)))) ∨ (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_231758456680631432619931729755 : (((p3 ∧ p2) → True) → (p2 ∨ (p5 → ((((False ∨ ((p4 ∨ p3) → (p3 → (True ∧ p4)))) ∨ (p4 → p4)) → p4) ∨ (p5 ∨ (p2 ∨ False)))))) := by
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
theorem thm_5_vars_315641844743443504448776326275 : (p3 ∨ ((True ∧ p5) ∨ ((True → (((True ∧ False) → ((False → (p5 ∨ p5)) → True)) → (p2 ∨ (p4 ∧ (p3 → p1))))) → (p4 ∨ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ False) → ((False → (p5 ∨ p5)) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184967519565777065065992974875 : (((p3 ∧ (p1 ∨ p3)) → ((p2 ∨ p5) → ((p5 ∧ p2) ∨ False))) ∨ (True ∨ (((True → (False ∨ True)) → p2) ∨ (p4 ∧ ((p1 ∨ p5) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59205344664428878646259004780 : (((p1 ∨ p3) ∨ (((((False ∧ True) ∨ True) ∧ p4) ∧ (p4 ∧ (((True ∧ p3) ∧ True) ∧ (((p5 → p4) ∨ p2) → p5)))) ∨ (p4 ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_56409258589841123778820286334 : ((((False → (p3 ∧ False)) → p1) → (((True ∨ False) ∧ False) ∨ (((p3 → (True → (p1 → False))) ∨ (p4 → p4)) ∨ ((p2 ∧ p1) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137886628118022942261019911836 : ((p4 ∨ ((p3 → (((p1 ∨ (((p1 → (p3 ∧ True)) ∨ ((p3 ∨ p3) ∧ (False → p3))) → p1)) → p5) → False)) ∨ True)) ∨ ((p3 → p1) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300559801787272833265410958119 : (False ∨ ((((p2 → p5) → p5) → ((p1 ∨ (((p2 ∨ ((False ∨ True) ∧ (True ∧ p3))) ∨ p1) ∧ p4)) ∧ p5)) ∨ (p5 → (True ∨ (p4 ∧ True))))) := by
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
theorem thm_5_vars_263101738671651499713240993373 : (True ∧ ((((p2 ∧ ((p1 → p5) ∨ (False ∨ ((p4 ∧ (p4 → ((True → True) ∧ (p5 → p2)))) ∨ p4)))) ∨ True) ∨ (p2 → p3)) ∨ (p3 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322704750703199830649299527801 : (p5 ∨ (((((((True ∧ p4) ∨ p3) ∧ (p4 ∧ ((p3 ∨ (((p2 ∧ p3) ∨ (p3 → False)) ∨ p4)) → (True → False)))) → p5) ∨ True) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∧ p4) ∨ p3) ∧ (p4 ∧ ((p3 ∨ (((p2 ∧ p3) ∨ (p3 → False)) ∨ p4)) → (True → False)))) → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893932468275880453406521030181 : (((((True ∨ p3) → (((p3 → (p5 ∧ False)) ∨ (((p2 ∨ ((True → (p5 ∨ True)) ∧ p5)) ∧ False) → p3)) ∧ p4)) ∧ (False → (p3 ∨ p5))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185201892562599001055210864352 : ((True ∧ ((p3 ∨ (p5 ∨ p2)) ∨ (p1 ∧ (True ∧ (p3 ∧ p4))))) ∨ (False → (((((p4 → p2) ∨ (p4 ∨ (p1 ∧ p1))) ∧ p4) ∨ True) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h1
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805438769456276781219571966775 : (((p3 → (p2 ∨ (((True ∨ (((p4 ∨ (((p4 ∧ True) → True) → p5)) → p5) → p1)) ∧ ((p5 ∨ ((p1 ∧ p5) ∨ False)) ∨ p2)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67327520949354668355695454126 : ((p1 → (((p1 ∧ (p2 ∧ ((((True ∧ (p4 → ((((p1 → p4) ∧ p1) ∧ p5) ∨ p3))) ∨ p3) ∧ (p3 ∨ p4)) → False))) ∨ p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596324534954491221605839015925 : (((((((p1 → p4) ∨ (p3 ∨ (p1 ∧ p4))) ∨ p3) ∨ (((True → (True ∨ False)) ∧ (p1 ∧ (((False ∧ p4) → p3) ∧ p3))) ∨ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315479806088293941403139609802 : (p3 ∨ (((p2 ∨ True) → p1) → ((((False ∨ True) ∨ p5) ∨ True) ∧ ((((p3 → p4) ∨ p4) ∨ ((p4 ∧ ((p5 ∧ p2) ∨ p5)) ∨ p2)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : (p2 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h20 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h20
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h23 : (p2 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h24 := h1 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683916395767059242446424489969 : (((((((((p4 → p1) → (p5 ∧ True)) ∧ p4) → (((True → p3) ∧ p3) ∧ p2)) ∧ p3) → False) ∨ (((p4 ∧ p1) ∧ p3) → (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321551375631709246856844824043 : (p4 ∨ (p2 → (((p4 ∧ p4) ∧ (p4 ∧ ((p5 ∧ p3) ∨ ((((p5 ∧ p2) ∨ p3) ∧ p2) ∨ (p2 ∨ (p4 ∨ True)))))) ∨ (p5 → (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_751169958205759660901303517575 : (((True ∧ (((p3 ∧ p1) → p4) ∨ (((p4 → ((((p1 ∨ p4) → p4) ∧ p2) ∨ p3)) → True) → (((p4 ∧ (p3 ∧ p2)) ∨ p5) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188282784285135824331587312983 : (((p3 ∨ (((p3 ∨ False) ∧ (False ∧ p1)) → p3)) ∨ p5) ∧ ((False ∧ (p5 ∧ ((p5 ∨ p5) ∧ (p5 ∧ (p5 ∧ (p1 → (p2 ∧ p5))))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313969661428290666074350018915 : (p3 ∨ (((((p1 ∧ p4) → False) → (((p3 ∧ (p2 ∨ p4)) → (False ∨ False)) → (True ∨ False))) → ((p5 → p1) ∧ (True → p4))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234383341838768085149013112600 : ((p1 → (True → p5)) → ((((True ∧ ((p2 ∨ True) ∨ False)) ∧ (p2 → False)) ∨ (p2 ∧ False)) → ((p3 ∧ p5) ∨ (p1 → ((True ∨ p1) → True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655701390915079483582166924652 : ((((((p1 → p1) → (p4 ∧ (((p3 ∨ p3) → p1) → (((p3 → p2) → (p2 → p4)) ∧ p2)))) ∧ (p5 ∧ (p5 ∨ p3))) ∨ (True ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607199261319981641702525184253 : ((((((False → ((p1 → (False ∧ p5)) ∨ p4)) → (p4 ∧ ((((p5 → (p1 ∧ p4)) ∧ False) ∧ (p2 ∨ (False ∧ p4))) ∧ False))) ∧ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56737865303119934344034852410 : ((((p5 ∨ p1) ∨ p4) ∧ ((False ∧ (p5 ∧ ((p4 → (p5 ∧ p2)) ∧ ((p3 → ((True → (p1 ∨ p4)) ∨ p5)) → p3)))) ∨ (True ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207945529679609677571009854213 : (((p1 → (p1 ∧ p4)) ∧ (p2 ∧ p5)) → (((p3 ∨ p3) ∧ (((p2 ∨ ((p1 ∨ True) → False)) ∨ p1) ∧ ((False → p2) → (False ∧ True)))) → p4)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h14 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h16 := h7 h14
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h23 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h24 := h18 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h30 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h31 := h26 h30
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h4.left
    let h35 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h1.left
        let h39 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h42 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h43
          -- False on the left can always be used.
          apply False.elim h43
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h44 := h35 h42
        -- We need to get the left conjuct of h44 based on <expert-advice>.
        let h45 := h44.left
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h1.left
        let h48 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
        have h51 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h46, we can now drive its conclusion.
        let h52 := h46 h51
        -- False on the left can always be used.
        apply False.elim h52
    case inr h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h1.left
      let h55 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h56 := h55.left
      let h57 := h55.right
      -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
      have h58 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h53
      -- We have shown the premise of h54, we can now drive its conclusion.
      let h59 := h54 h58
      -- We need to get the right conjuct of h59 based on <expert-advice>.
      let h60 := h59.right
      -- One of the premise coincides with the conclusion.
      exact h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171598566960717748832918094067 : (((((p5 ∨ (False ∨ p4)) ∨ (p5 ∧ p1)) ∧ (((p1 ∧ p1) ∨ True) ∨ p5)) ∨ False) ∨ ((((((p2 ∧ p4) ∨ p3) → False) ∧ False) ∧ p2) → False)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762946605978689638331722739780 : (((p3 ∧ ((p5 ∨ (p1 ∧ (p4 ∨ p4))) ∧ (False ∨ ((((p5 → (False ∨ ((p3 ∧ False) ∨ False))) ∧ p2) ∧ ((p2 ∨ False) ∨ p3)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42485871954669229915023664672 : (((False ∨ (((((((True ∨ ((p1 → p2) ∨ p1)) ∨ p1) → (p1 ∨ False)) ∨ False) ∧ ((p2 ∨ p5) ∧ (True → True))) ∧ p1) ∧ p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774644898610726202822507291064 : (((False ∨ (((p3 → ((((p1 ∧ p2) ∧ p5) → p2) ∧ False)) → p4) ∨ (((p1 ∧ (p1 → (p5 → False))) ∨ (True ∨ p3)) ∨ (p4 ∧ p2)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118147234183519379481579487453 : ((False ∨ ((False ∧ (p5 ∧ (((True ∧ p2) ∨ (p2 ∧ p2)) → False))) ∨ ((((p2 → p1) → (p2 ∧ (True → p3))) ∧ True) ∨ p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792761038469922463215059227407 : (((True → ((p3 ∧ ((True → p2) → True)) → ((False ∧ (p1 → ((p4 ∧ p3) ∨ (((True → (p3 → False)) → p3) ∧ (p1 → p5))))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160261305034798664981020177862 : (((False ∨ (((True ∨ (p3 ∨ p2)) ∨ ((p1 ∨ (True ∨ p1)) → (p2 → p4))) ∧ p3)) ∨ (False ∧ p3)) → (p4 ∨ (p1 ∨ ((p5 → p3) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h9
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h12
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h14
            -- One of the premise coincides with the conclusion.
            exact h6
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119510988775755681247860846269 : ((p5 → ((((False ∧ p4) ∧ ((p1 ∨ True) ∨ p5)) ∨ (p3 ∨ (p4 → ((p1 ∨ p5) ∧ ((True → (p1 ∨ p5)) ∨ p3))))) ∧ True)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_474508997499969456525284191114 : (((((((p3 → p2) ∧ (True ∧ (p1 ∧ False))) ∨ False) → False) ∧ ((p5 → p1) ∨ (((p4 → p4) ∨ p4) → ((True ∧ False) ∨ (p1 ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192008190357219076529214272026 : ((p1 → (False ∧ (False ∨ ((p5 → (False ∧ p5)) → True)))) ∨ (((p2 ∧ (p2 ∨ ((p2 ∨ (p3 ∨ p3)) → (True ∨ (p5 → p5))))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230264191610704904560185456418 : (((False ∨ p2) ∧ p1) → ((p1 → p4) → ((((((p3 ∨ (p4 → p4)) ∧ ((False → p5) ∨ False)) ∨ p3) → (True → (p3 → p3))) → p5) ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137304551395826013219931259696 : ((p2 ∧ (((((False ∨ (((p1 ∨ (p1 → False)) ∧ p4) ∨ False)) ∨ p2) → (True ∨ p4)) → False) ∨ (p2 → (True ∧ p4)))) ∨ (p2 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115727329155569249789733607293 : ((((p4 → (p5 → (True ∧ p2))) → True) → (((p2 ∧ (p1 ∧ (p1 ∨ ((p5 ∨ p3) → (p3 ∨ p4))))) ∧ p1) ∨ (p1 ∧ p2))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307435455254121981383461806431 : (p1 ∨ (p5 ∨ ((((p1 ∧ ((p3 ∨ (True ∧ p2)) ∧ (p3 → p3))) ∨ p5) ∧ (((p2 → False) → (p4 ∧ p3)) ∨ (p2 → False))) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_322271879881216342766421305453 : (p5 ∨ (((True → (True → ((False ∧ ((p4 ∧ p3) ∧ p2)) ∨ (((p2 ∨ p5) ∨ (False ∨ (((p5 ∨ True) ∨ p4) ∧ p5))) → False)))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310159042080996136662363042264 : (p2 ∨ (((p2 ∧ p1) ∨ ((((p2 ∧ p4) ∨ p1) ∨ (p1 ∧ (p4 → p2))) ∨ p3)) → ((False ∨ ((False → p5) → p2)) ∨ (True ∧ (p2 → True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56880986087306062443566466648 : (((p2 ∧ (p1 ∨ p2)) ∧ (((p4 → (p5 ∨ p5)) ∧ (((((p3 ∧ p1) ∧ True) ∨ False) → (p3 ∧ p2)) ∧ (p4 ∧ (p1 → p1)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173156848647636035492573669693 : ((p3 ∨ (p2 ∧ ((True → (p3 ∨ (p4 ∨ ((p2 ∨ p5) ∧ (p5 ∧ p2))))) ∧ False))) ∨ (True ∨ (p4 ∧ (((p4 → p5) → True) ∧ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159044901627935417025543401828 : ((p5 ∨ ((((p4 ∨ False) ∧ (((p3 ∧ False) ∨ p3) ∨ p3)) ∨ (p1 ∨ (p5 ∨ (False ∨ True)))) ∨ p3)) ∨ ((p3 ∧ (p5 → p1)) → (True ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65738861574133143836527003035 : ((p4 ∨ ((((True ∧ ((((p4 ∧ (((True → p5) ∧ p5) ∨ False)) ∧ p5) ∨ p1) → p1)) ∨ (p5 → p3)) ∧ p5) ∨ ((True ∧ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687823734396417860859383850770 : (((((p3 → ((p5 ∧ (False ∨ ((p2 → p3) ∧ (False ∨ p4)))) → p3)) → (True → p4)) ∧ ((p5 → (p3 ∧ (True ∧ p4))) → (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777852335295944747298552928451 : (((p1 ∨ ((p5 ∧ ((p5 → p4) → p5)) ∨ ((p3 → ((p2 ∨ (((p1 ∨ p3) → True) ∨ p3)) ∧ (False ∧ (p3 → (p2 → p5))))) ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_203470874614741824089325274046 : ((True ∨ ((p2 ∨ p4) ∨ (p5 ∨ False))) ∧ (p4 → ((p2 ∨ (((False → (((p5 → p1) → False) ∨ (p4 ∧ p1))) → (p5 ∧ p5)) ∧ False)) ∨ True))) := by
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
theorem thm_5_vars_252874196557721916203660460281 : ((True ∧ p1) → ((((p2 ∧ (((p5 ∧ p5) → p1) → (False ∨ p4))) ∧ p5) ∧ (p1 ∧ (p4 ∧ ((p3 ∨ (p3 ∨ (p2 ∨ p2))) ∨ p5)))) ∨ True)) := by
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
theorem thm_5_vars_247309226845553787354986422880 : ((False ∨ False) ∨ ((((((p3 → p3) ∧ p2) ∧ True) ∨ p4) → (p5 ∨ True)) ∧ ((p4 ∨ p1) → (((False → p4) → (p4 ∧ p5)) → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h16 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h16
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179723486405286750504194575414 : ((((((p5 ∧ p5) ∧ (p4 → p2)) ∧ (p5 → (p5 ∧ False))) → p1) ∧ p2) → (((True → p1) ∨ (False → p4)) ∨ ((p2 ∧ True) → (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64811879671013395179159143957 : ((p2 ∨ ((((((p1 → p1) ∧ True) ∨ False) ∨ ((p3 → p2) ∨ ((((p4 ∨ p1) → ((False ∧ p4) ∨ p4)) ∧ p4) ∨ p4))) ∧ True) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137962400565577557667361209211 : ((p5 ∨ ((p4 ∧ ((False ∨ ((p5 → p3) → (p3 ∧ p3))) ∨ (p3 ∨ (p1 ∨ (False ∨ (p4 ∧ p4)))))) ∨ (p5 ∧ p4))) ∨ ((False → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207959675811041926117493513927 : (((p5 → (True → True)) ∧ (p2 → True)) → (p1 → (((((p1 ∨ (((p5 → p2) → p4) → True)) ∧ (True ∧ (p2 ∨ False))) ∨ p4) ∨ p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118112385382337854675873602871 : ((False ∨ (((((p1 → p2) → ((((((p5 ∨ True) → (p3 ∨ p4)) ∧ p5) ∧ (p5 ∨ p5)) ∧ True) ∧ p1)) → p1) → p5) → False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391560488018652971293955513505 : ((((((p5 ∧ True) → (False ∧ p4)) ∧ (p2 ∨ (True ∧ (p1 ∧ ((p2 ∧ (p2 → p4)) ∧ ((True → (p3 → p1)) ∨ (p1 ∧ p5))))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_134835911855512989404553779558 : (((p2 ∨ (False → (p2 ∧ ((p5 → (p3 → p1)) ∨ ((True → (p1 ∨ ((p5 ∨ p2) ∨ p1))) → (False ∨ p4)))))) → p4) ∨ ((p3 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307848852648124981782736797469 : (p1 ∨ (p5 → (((True → ((p4 ∨ ((True ∧ p2) ∧ p2)) ∨ ((True → p1) ∧ ((True ∨ (p3 ∧ (False ∨ p5))) ∨ p4)))) ∨ (p5 ∨ False)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233679166115783673342109273979 : ((p2 ∨ (False → p3)) → (p4 ∨ ((p1 ∨ (p2 → (p3 ∨ (((False ∧ (False → p3)) ∧ (p5 ∨ p5)) → ((p4 → (p4 ∧ False)) ∧ p4))))) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the left can always be decomposed.
    let h14 := h4.left
    let h15 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- False on the left can always be used.
    apply False.elim h24
    -- Conjunctions on the left can always be decomposed.
    let h26 := h20.left
    let h27 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- False on the left can always be used.
    apply False.elim h28
    -- Conjunctions on the left can always be decomposed.
    let h30 := h20.left
    let h31 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218640086059436568161273124887 : ((True ∧ ((p4 ∨ p4) ∨ False)) → ((((p3 ∨ p3) ∨ p3) ∨ (True ∧ (True → (p4 ∨ (((p5 → True) ∨ (False → (p4 ∨ p1))) → True))))) ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306445954681283512325198813369 : (p1 ∨ ((p1 ∨ p4) ∨ (p5 ∨ (((p1 ∨ ((True ∨ p1) ∨ p1)) ∧ p3) ∨ (((p1 ∧ p1) ∧ ((p3 → p1) ∨ (p2 ∨ (p3 ∧ p5)))) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40642844288147178165251934386 : (((((True ∧ ((p3 ∧ p5) ∧ ((p5 ∧ True) ∨ (False ∧ (True → ((p5 ∧ True) → (True ∨ (p1 → (p1 ∧ False))))))))) → p2) → p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114204566788514038823777362810 : ((((p1 → (p1 ∨ (False ∧ True))) ∧ (True → ((((p4 ∧ (p5 → p1)) ∨ (True → p2)) → p5) ∨ True))) → ((False ∧ True) ∨ p4)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682895908548780712807010059490 : (((((p3 ∨ True) ∧ ((p5 ∧ (p2 → p1)) → ((p5 ∧ (p4 ∧ (True → (True ∨ True)))) ∨ p1))) ∧ ((p4 ∧ p1) ∨ (True ∨ (p4 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692856179363699194192906893777 : ((((((p3 ∨ p3) ∧ p1) → (p3 → (((True ∧ (p3 → False)) ∧ p5) ∧ p3))) ∧ (((((False → p4) → (p2 ∨ p5)) ∨ False) ∨ p3) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138312625820394040760681669357 : ((p3 → (((p3 ∧ p5) → p4) → ((((p3 → (p1 → (p4 ∨ ((False ∧ p2) ∨ p2)))) ∧ p3) ∨ (p4 ∨ True)) ∨ p4))) ∨ (p5 → (True → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41412123200263798039291256723 : ((((((True → (True ∨ (p3 ∨ p3))) ∨ p4) ∧ ((p5 → True) → (True → p1))) ∨ (((False ∧ (p5 → p3)) ∧ (p4 ∨ p2)) ∨ True)) ∨ p5) ∨ False) := by
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
theorem thm_5_vars_193794649524792825483004176081 : ((p4 ∧ (p3 ∧ (((p5 ∨ p1) ∨ (p4 ∨ p5)) ∨ p2))) → (((p5 → (p3 ∨ (False ∧ False))) → ((p3 → (p5 ∧ True)) ∧ p4)) ∨ (True ∧ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234388922897754684768320030922 : ((p1 → (False → p5)) → (((p2 ∧ ((((p4 → p4) ∧ p5) → (True ∧ p2)) ∨ p4)) ∨ ((False ∧ p1) ∨ p5)) → ((False → p3) ∧ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690343786461553065436933314816 : ((((p3 → ((p1 → (p2 ∨ (p5 → p4))) → (((p1 ∨ (p4 ∨ True)) ∧ p4) ∨ p4))) ∨ ((True → False) ∨ (p5 ∨ (p5 → (True ∨ True))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244647679752417386398197368498 : ((False ∧ p5) ∨ ((p4 ∧ True) ∨ (((p1 ∨ False) → (False ∧ p5)) ∨ (((p2 ∧ p5) → (p1 ∨ p5)) → (p1 ∨ (False → (p4 ∧ (True ∨ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_238206639359138350464172654990 : ((True ∨ p4) ∧ (((p4 ∧ p5) ∧ True) ∨ (True → (p3 ∨ ((p5 ∧ p3) ∨ ((p5 ∧ (p4 → ((((False ∨ p3) ∨ True) ∨ p2) ∨ p2))) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37332129606434445516953452954 : (((((((((p2 → (p5 ∨ False)) ∨ (p3 → True)) → True) → ((p1 → p4) ∨ p5)) ∧ (False ∨ (p4 ∨ (p2 ∨ p2)))) ∧ p2) ∨ False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116491340039494857665987070711 : (((p2 ∧ p4) ∧ (True → (((p1 ∧ False) → ((p2 ∧ (p4 ∨ (p5 → p5))) ∨ (p3 ∨ (p4 → (p1 → (p5 ∧ p1)))))) → p4))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358471647104146255533537128865 : (p5 → (p1 → ((p3 ∧ (p4 ∧ (((p4 ∧ (((True → p4) → p4) → p3)) ∧ p3) ∨ ((p3 → p3) ∨ ((True ∨ True) ∨ p3))))) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114731138735568610001860023292 : (((((True ∧ p4) ∨ ((True → p4) ∧ p5)) ∧ (p1 → (False ∧ ((p1 → p2) ∧ False)))) → (p2 ∨ (((p3 ∧ p5) ∨ True) ∧ True))) ∨ (p1 ∧ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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
theorem thm_5_vars_665395918072373468595037666817 : (((((p2 ∨ (((p4 ∨ p4) ∨ (p2 → (False ∧ (p3 ∧ False)))) ∨ ((p3 ∧ (p5 ∨ (False ∨ p4))) ∧ True))) ∧ False) ∧ (True ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114474189394451705302793989402 : ((((p2 ∧ (False ∧ ((p5 ∨ (((False → p4) ∨ p5) ∧ (p3 → p4))) → (p2 → p2)))) → p1) → ((p5 ∨ p3) ∨ (p3 ∨ p3))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165734583003788195765355894928 : ((((p5 ∨ (p2 ∨ p4)) ∧ p5) ∨ (p3 → (p5 → (p2 ∧ (p2 ∨ (p2 → (p4 ∨ False))))))) ∨ (((False ∨ (False ∨ False)) ∧ p1) → (p4 ∨ True))) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328198869606419522661079245202 : (True → (((True ∨ p3) ∧ ((p2 ∨ (p1 → ((p4 ∧ (p2 ∨ ((p2 ∧ False) ∧ ((p4 → p1) ∨ p4)))) ∧ p2))) ∨ p2)) → ((True → p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h10 := h3 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h12
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h23
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h26
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178864341916746235636102980560 : (((p1 → (p1 ∧ p3)) → (((False ∧ p5) ∨ p5) ∧ (p2 → (p4 → p2)))) ∨ ((((p1 ∨ p1) ∧ (p5 ∧ (p1 ∧ (p1 ∨ p3)))) ∧ p2) → p5)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159039955243164893496899972393 : ((p5 ∨ (((p5 ∨ ((p2 → p2) ∨ (False ∨ ((p5 ∧ ((p3 ∨ False) ∨ p2)) ∧ p2)))) ∧ p2) ∧ p3)) ∨ (((p1 ∧ p1) ∧ True) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



